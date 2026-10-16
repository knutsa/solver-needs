"""Text-level handling of Verus sources: assert statements, their terms and functions.

Like the Dafny side, the pipeline works on text: ``assert`` statements are
located by character range, expressions are split at top-level operators
(after masking turbofish generics so ``<`` can be split on), and the
function a statement belongs to is found by scanning for ``fn`` headers.
"""

import re

from solver_needs.config import MAX_SEEDS
from solver_needs.dafny.source import assert_span, strip_comments, unwrap_parens

ASSERT_RE = re.compile(r"(?<![\w'])assert\b(?!!)")  # the Rust macro assert! is never a candidate
STATEMENT_HEAD_RE = re.compile(r"=>$")  # assert as a match-arm body
FN_RE = re.compile(
    r"^[ \t]*(?:pub(?:\([^)]*\))?\s+)?(?:(?:open|closed|uninterp)\s+)?"
    r"(?:(?:proof|spec|exec|broadcast\s+proof)\s+)?fn\b",
    re.M,
)
BOOL_OPS = ("<==>", "==>", "&&&", "|||", "&&", "||")
EQ_OPS = ("=~~=", "=~=", "==")
CMP_OPS = EQ_OPS + ("!=", "<=", ">=", "<", ">")
BINDER_RE = re.compile(r"\b(forall|exists|choose)\s*\||\bold\s*\(")
NONLINEAR_RE = re.compile(r"[/%]|(?<![\d_])\s*\*\s*(?![\d_])")
TRIVIAL_RE = re.compile(
    r"[\w'.@:]+|-?[\d_]+(\.\d+)?(nat|int|u\d+|i\d+|usize|isize)?|\"[^\"]*\"|'[^']*'"
    r"|true|false|\w+\s+as\s+\w+"
)
COLLECTION_METHODS = {
    "subrange",
    "push",
    "add",
    "update",
    "insert",
    "remove",
    "take",
    "skip",
    "drop_last",
    "drop_first",
    "reverse",
    "filter",
    "map",
    "map_values",
    "to_seq",
    "view",
    "empty",
    "new",
}
COLLECTION_HEAD_RE = re.compile(r"^(seq!|set!|map!|Seq|Set|Map|Multiset)")


# ---------------------------------------------------------------- generics masking


def mask_generics(text: str) -> tuple[str, dict[str, str]]:
    """Replace turbofish generics ``::<...>`` by word-like tokens so ``<`` can be split on."""
    out, table, i, n = [], {}, 0, 0
    while i < len(text):
        if text.startswith("::<", i):
            depth, j = 0, i + 2
            while j < len(text):
                depth += text[j] == "<"
                depth -= text[j] == ">"
                j += 1
                if depth == 0:
                    break
            token = f"__G{n}__"
            table[token] = text[i:j]
            out.append(token)
            n += 1
            i = j
            continue
        out.append(text[i])
        i += 1
    return "".join(out), table


def unmask(text: str, table: dict[str, str]) -> str:
    """Undo ``mask_generics``."""
    for token, original in table.items():
        text = text.replace(token, original)
    return text


# ---------------------------------------------------------------- terms


def top_level_split(text: str, ops: tuple[str, ...]) -> list[str]:
    """Split ``text`` on any of ``ops`` occurring outside brackets and closures."""
    parts, depth, i, cur = [], 0, 0, ""
    while i < len(text):
        ch = text[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        if depth == 0:
            hit = next((op for op in ops if text.startswith(op, i)), None)
            if hit:
                parts.append(cur)
                cur = ""
                i += len(hit)
                continue
        cur += ch
        i += 1
    parts.append(cur)
    return [p.strip() for p in parts if p.strip()]


def bracketed_subterms(text: str) -> list[str]:
    """Maximal ``f(...)``, ``x[...]``, ``a.b(...).c[...]`` subterms, outermost first."""
    found, i = [], 0
    head = re.compile(r"[A-Za-z_][\w.@':]*|\(")
    while i < len(text):
        m = head.match(text, i)
        if not m:
            i += 1
            continue
        start = m.start()
        j = m.end() if m.group() != "(" else start
        contents = []
        while j < len(text) and text[j] in "([.@":
            if text[j] == "@":
                j += 1
                continue
            if text[j] == ".":
                tail = re.match(r"\.[A-Za-z_]\w*", text[j:])
                if not tail:
                    break
                j += tail.end()
                continue
            close = {"(": ")", "[": "]"}[text[j]]
            depth, k = 0, j
            while k < len(text):
                depth += text[k] in "([{"
                depth -= text[k] in ")]}"
                if depth == 0:
                    break
                k += 1
            if k >= len(text) or text[k] != close:
                break
            contents.append(text[j + 1 : k])
            j = k + 1
        term = text[start:j].strip()
        paren_only = m.group() == "(" and len(contents) == 1 and term.endswith(")")
        if contents and not paren_only:
            found.append(term)
            for inner in contents:
                found.extend(t for t in bracketed_subterms(inner) if t not in found)
            i = j
        else:
            i = max(j, m.end())
    return found


def is_trivial(term: str) -> bool:
    """Literals, bare paths and casts: never worth seeding."""
    return TRIVIAL_RE.fullmatch(term) is not None


def has_binder(term: str) -> bool:
    """Quantifiers, ``choose`` and ``old`` cannot be seeded as terms."""
    return BINDER_RE.search(term) is not None


def candidate_terms(expr: str) -> list[str]:
    """Seedable subterms for the INST probe: comparison operands and bracketed subterms."""
    terms: list[str] = []
    for atom in top_level_split(expr, BOOL_OPS):
        atom = unwrap_parens(atom)
        if has_binder(atom) or atom.startswith("!"):
            continue
        for operand in top_level_split(atom, CMP_OPS):
            operand = unwrap_parens(operand)
            if len(top_level_split(operand, BOOL_OPS + CMP_OPS)) > 1:
                terms += [t for t in candidate_terms(operand) if t not in terms]
                continue
            if not is_trivial(operand) and operand not in terms:
                terms.append(operand)
            for sub in bracketed_subterms(operand):
                if sub != operand and not is_trivial(sub) and sub not in terms:
                    terms.append(sub)
    return terms[:MAX_SEEDS]


def equality_atoms(expr: str) -> list[tuple[str, str, str]]:
    """Top-level equality atoms as ``(op, a, b)`` with op in ``=~~=``, ``=~=``, ``==``."""
    atoms = []
    for atom in top_level_split(expr, BOOL_OPS):
        atom = unwrap_parens(atom)
        if has_binder(atom):
            continue
        for op in EQ_OPS:
            sides = top_level_split(atom, (op,))
            if len(sides) == 2 and len(top_level_split(atom, CMP_OPS)) == 2:
                atoms.append((op, sides[0], sides[1]))
                break
    return atoms


def is_collection_text(side: str) -> bool:
    """Outermost shape of ``side`` is a collection constructor, view or method call."""
    side = unwrap_parens(side.strip())
    if side.endswith("@") or COLLECTION_HEAD_RE.match(side):
        return True
    if not side.endswith(")"):
        return False
    depth = 0
    for i in range(len(side) - 1, -1, -1):
        depth += side[i] in ")]}"
        depth -= side[i] in "([{"
        if depth == 0:
            method = re.search(r"\.(\w+)$", side[:i])
            return method is not None and method.group(1) in COLLECTION_METHODS
    return False


def shape_from_text(expr: str, tactic: str | None) -> dict:
    """Is the assertion an equality between collections, and is it nonlinear."""
    masked, table = mask_generics(expr)
    atoms = [(op, unmask(a, table), unmask(b, table)) for op, a, b in equality_atoms(masked)]
    return {
        "collection_eq": any(
            op != "==" or is_collection_text(a) or is_collection_text(b) for op, a, b in atoms
        ),
        "nonlinear": tactic == "nonlinear_arith" or NONLINEAR_RE.search(expr) is not None,
        "from_ast": False,
    }


# ---------------------------------------------------------------- statements


def statement_end(text: str, begin: int) -> int:
    """One past the end of the assert statement starting at ``begin``.

    Ends at the first ``;`` outside brackets, or at the ``}`` closing the
    first block ``{ ... }`` outside brackets (a ``by { }`` body or the block
    after ``by(nonlinear_arith) requires ...``), plus an optional ``;``.
    """
    depth, i = 0, begin
    while i < len(text):
        if text.startswith("//", i):
            i = text.find("\n", i)
            i = len(text) if i < 0 else i
            continue
        ch = text[i]
        if depth == 0 and ch == ";":
            return i + 1
        if depth == 0 and ch == "{":
            d, j = 0, i
            while True:
                d += text[j] == "{"
                d -= text[j] == "}"
                if d == 0:
                    break
                j += 1
            j += 1
            while j < len(text) and text[j] in " \t":
                j += 1
            return j + 1 if j < len(text) and text[j] == ";" else j
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        i += 1
    raise ValueError(f"unterminated assert statement at offset {begin}")


def assert_statements(text: str) -> list[tuple[int, int]]:
    """``(begin, end)`` offsets of every ghost assert statement, by-block bodies included."""
    clean = strip_comments(text)
    spans = []
    for m in ASSERT_RE.finditer(clean):
        before = clean[: m.start()].rstrip()
        if before and before[-1] not in "{};)" and not STATEMENT_HEAD_RE.search(before):
            continue
        end = statement_end(clean, m.start())
        spans.append((m.start(), end))
    return spans


def block_body(text: str) -> str | None:
    """Contents of the first ``{ ... }`` block outside brackets, or None."""
    depth = 0
    for i, ch in enumerate(text):
        if depth == 0 and ch == "{":
            return text[i + 1 : text.rstrip(";").rstrip().rfind("}")].strip()
        depth += ch in "([{"
        depth -= ch in ")]}"
    return None


def split_assert(statement: str) -> dict:
    """Parse an assert statement: kind (plain or forall), expression, by-block body, tactic."""
    text = re.sub(r"//[^\n]*", "", statement).strip()
    text = re.sub(r"^assert\b\s*", "", text)
    if text.startswith("forall"):
        m = re.search(r"\bby\s*\{", text)
        head = text[: m.start()].strip() if m else text.rstrip(";").strip()
        return {"kind": "forall", "expr": head, "by_body": block_body(text), "tactic": None}
    depth, j = 0, 0
    for j, ch in enumerate(text):  # noqa: B007 - j, the closing paren, is used after the loop
        depth += ch == "("
        depth -= ch == ")"
        if depth == 0:
            break
    rest = text[j + 1 :].strip()
    tactic = re.match(r"by\s*\(\s*(\w+)\s*\)", rest)
    return {
        "kind": "plain",
        "expr": text[1:j].strip(),
        "by_body": block_body(rest),
        "tactic": tactic.group(1) if tactic else None,
    }


def inner_assert_exprs(body: str) -> list[str]:
    """Expressions of the assert statements inside a by-block body."""
    lines = body.split("\n")
    exprs, i = [], 0
    while i < len(lines):
        if lines[i].strip().startswith("assert"):
            end = assert_span(lines, i)
            exprs.append(split_assert("\n".join(lines[i : end + 1]))["expr"])
            i = end + 1
            continue
        i += 1
    return exprs


def in_proof_context(text: str, pos: int) -> bool:
    """Is ``pos`` inside a proof fn, spec fn, proof block or assert-by block?"""
    depth = 0
    for i in range(pos - 1, -1, -1):
        ch = text[i]
        if ch == "}":
            depth += 1
        elif ch == "{":
            if depth > 0:
                depth -= 1
                continue
            before = text[:i].rstrip()
            if re.search(r"\b(proof|by)$", before):
                return True
            header = re.search(r"\bfn\s+\w+[^{;]*$", before)
            if header:
                signature = before[max(0, header.start() - 40) : header.start()]
                return re.search(r"\b(proof|spec)\s*$", signature) is not None
    return False


def recursive_spec_fns(text: str) -> set[str]:
    """Names of the spec fns with a ``decreases`` clause (the FUEL probe's candidates)."""
    return {
        m.group(1)
        for m in re.finditer(r"\bspec\s+fn\s+(\w+)\s*(?:<[^>]*>)?\s*\([^{]*?\bdecreases\b", text)
    }


# ---------------------------------------------------------------- functions


def enclosing_fn_lines(clean: str, offset: int) -> tuple[int, int]:
    """``(first, last)`` 1-based line of the function containing ``offset``.

    A function starts on its own line and extends to the line before the
    next function start (or the end of the file); braces are not tracked,
    the rule the Dafny side uses for declarations.
    """
    starts = [m.start() for m in FN_RE.finditer(clean)]
    before = [b for b in starts if b <= offset]
    if not before:
        raise ValueError(f"no enclosing function at offset {offset}")
    after = [b for b in starts if b > offset]
    first = clean.count("\n", 0, before[-1]) + 1
    last = clean.count("\n", 0, after[0]) if after else clean.count("\n") + 1
    return first, last

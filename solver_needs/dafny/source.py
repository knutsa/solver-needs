"""Text-level handling of Dafny sources: assert statements, their terms and declarations.

The pipeline never parses Dafny; it locates ``assert`` statements by
character range, splits their expressions at top-level operators and finds
the declaration a statement belongs to by scanning for declaration keywords.
"""

import re

from solver_needs.config import MAX_SEEDS

ASSERT_RE = re.compile(r"(?<![\w'])assert\b")
STATEMENT_HEAD_RE = re.compile(r"(\bthen|\belse|=>)$")  # assert in expression position
LABELLED_RE = re.compile(r"^assert\s+(?:\{:[^}]*\}\s*)*\w+\s*:(?![:=|])")  # labels may be numeric
BOOL_OPS = ("==>", "<==>", "&&", "||")
CMP_OPS = ("==", "!=", "<=", ">=", "<", ">", " in ", " !in ")
DECL_RE = re.compile(
    r"^[ \t]*(?:(?:ghost|static|opaque|twostate|greatest|least|abstract)\s+)*"
    r"(?:method|lemma|function|predicate|constructor|iterator|class|trait|datatype|codatatype"
    r"|module|newtype|type)\b",
    re.M,
)


# ---------------------------------------------------------------- statements


def strip_comments(text: str) -> str:
    """Blank out comments and string literals, preserving offsets."""
    out = list(text)
    i = 0
    while i < len(text):
        if text.startswith("//", i):
            j = text.find("\n", i)
            j = len(text) if j < 0 else j
        elif text.startswith("/*", i):
            j = text.find("*/", i)
            j = len(text) if j < 0 else j + 2
        elif text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j += 1
        else:
            i += 1
            continue
        for k in range(i, min(j, len(text))):
            if out[k] != "\n":
                out[k] = " "
        i = j
    return "".join(out)


def code_only(line: str) -> str:
    """The line without a trailing ``//`` comment."""
    return line.split("//", 1)[0].rstrip()


def assert_span(lines: list[str], start: int) -> int:
    """Inclusive end index of the assert statement starting at line ``start``."""
    j = start
    while j < len(lines):
        code = code_only(lines[j]).strip()
        if "by {" in code or "by{" in code:
            depth = code.count("{") - code.count("}")
            while depth > 0:
                j += 1
                depth += code_only(lines[j]).count("{") - code_only(lines[j]).count("}")
            return j
        if code.endswith(";"):
            k = j + 1
            while k < len(lines) and code_only(lines[k]).strip() == "":
                k += 1
            if k < len(lines) and code_only(lines[k]).strip().startswith("by"):
                j = k
                continue
            return j
        j += 1
    raise ValueError(f"unterminated assert at line {start + 1}")


def _matching_close(text: str, open_idx: int) -> int:
    """Index one past the bracket matching the opening bracket at ``open_idx``."""
    depth = 0
    for j in range(open_idx, len(text)):
        depth += text[j] in "([{"
        depth -= text[j] in ")]}"
        if depth == 0:
            return j + 1
    raise ValueError(f"unbalanced bracket at offset {open_idx}")


def statement_end(text: str, begin: int) -> int:
    """Index one past the end of the assert statement starting at ``begin``.

    Ends at the first ``;`` outside brackets, or at the ``}`` closing a
    ``by {`` block that follows the expression. Comments are skipped.
    """
    depth, i = 0, begin
    while i < len(text):
        if text.startswith("//", i):
            newline = text.find("\n", i)
            i = len(text) if newline < 0 else newline
            continue
        ch = text[i]
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
            if depth < 0:
                raise ValueError(f"unbalanced assert statement at offset {begin}")
        elif depth == 0 and ch == ";":
            return i + 1
        elif depth == 0 and text.startswith("by", i) and not text[i - 1].isalnum():
            block = re.match(r"by\s*\{", text[i:])
            if block:
                return _matching_close(text, i + block.end() - 1)
        i += 1
    raise ValueError(f"unterminated assert statement at offset {begin}")


def assert_statements(text: str) -> list[tuple[int, int]]:
    """``(begin, end)`` offsets of every assert statement in statement position."""
    clean = strip_comments(text)
    spans = []
    for m in ASSERT_RE.finditer(clean):
        before = clean[: m.start()].rstrip()
        if before and before[-1] not in "{};)" and not STATEMENT_HEAD_RE.search(before):
            continue  # part of an expression, e.g. an identifier
        try:
            end = statement_end(clean, m.start())
        except ValueError:
            continue
        spans.append((m.start(), end))
    return spans


def is_labelled(statement: str) -> bool:
    """``assert L: E`` names a fact for a later ``reveal L``; never a candidate."""
    return LABELLED_RE.match(statement.strip()) is not None


def split_assert(statement: str) -> tuple[str, str | None]:
    """``(expression, by-block body or None)`` of an assert statement's text."""
    text = re.sub(r"//[^\n]*", "", statement).strip()
    text = re.sub(r"^assert\b", "", text).strip()
    text = re.sub(r"^\{:[^}]*\}\s*", "", text)
    match = re.search(r"\bby\s*\{", text)
    if match:
        expr = text[: match.start()].strip()
        body = text[match.end() : text.rstrip().rfind("}")].strip()
        return expr, body
    return text.rstrip(";").strip(), None


def inner_assert_exprs(body: str) -> list[str]:
    """Expressions of the assert statements inside a by-block body."""
    lines = body.split("\n")
    exprs, i = [], 0
    while i < len(lines):
        if lines[i].strip().startswith("assert"):
            end = assert_span(lines, i)
            exprs.append(split_assert("\n".join(lines[i : end + 1]))[0])
            i = end + 1
            continue
        i += 1
    return exprs


# ---------------------------------------------------------------- terms


def top_level_split(text: str, ops: tuple[str, ...]) -> list[str]:
    """Split ``text`` on any of ``ops`` occurring outside brackets."""
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
    """Maximal ``f(...)``, ``x[...]``, ``(...)[...]`` and ``a.b(...)`` subterms."""
    found, i = [], 0
    head = re.compile(r"[A-Za-z_][\w'.]*|\(")
    while i < len(text):
        m = head.match(text, i)
        if not m:
            i += 1
            continue
        j = m.end() if m.group() != "(" else m.start()
        start = m.start()
        while j < len(text) and text[j] in "([":
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
            j = k + 1
        term = text[start:j].strip()
        if j > m.end() and re.search(r"[(\[]", term):
            found.append(term)
            inner = term[m.end() - start :] if m.group() != "(" else term
            found.extend(t for t in bracketed_subterms(inner[1:-1]) if t not in found)
            if m.group() == "(":
                depth = 0
                for k, ch in enumerate(term):
                    depth += ch in "([{"
                    depth -= ch in ")]}"
                    if depth == 0:
                        found.append(term[1:k].strip())
                        break
            i = j
        else:
            i = m.end()
    return found


def unwrap_parens(term: str) -> str:
    """Strip one pair of parentheses if they enclose the whole term."""
    while term.startswith("(") and term.endswith(")"):
        depth = 0
        for i, ch in enumerate(term):
            depth += ch in "([{"
            depth -= ch in ")]}"
            if depth == 0 and i < len(term) - 1:
                return term
        term = term[1:-1].strip()
    return term


def is_trivial(term: str) -> bool:
    """Literals and bare identifiers: never worth seeding."""
    return (
        re.fullmatch(r"[\w'.]+|-?\d+(\.\d+)?|\"[^\"]*\"|'[^']*'|true|false|\[\]|\{\}", term)
        is not None
    )


def has_binder(term: str) -> bool:
    """Quantifiers, comprehensions, ``old`` and conditionals cannot be seeded as terms."""
    return (
        re.search(
            r"\b(forall|exists|old|fresh|unchanged|allocated|then|else)\b|::|=>"
            r"|\b(set|iset|map|imap)\s+\w+\s*[|:]",
            term,
        )
        is not None
    )


def candidate_terms(expr: str) -> list[str]:
    """Seedable subterms of an assertion for the INST probe.

    The expression is split at top-level Boolean operators and each atom at
    its comparison operator; every operand and every maximal bracketed
    subterm is a candidate, excluding literals, bare identifiers and
    anything containing a binder. Membership atoms are candidates as a
    whole. At most ``MAX_SEEDS`` terms are kept, in order of appearance.
    """
    terms: list[str] = []
    for atom in top_level_split(expr, BOOL_OPS):
        if has_binder(atom):
            continue
        operands = top_level_split(atom, CMP_OPS)
        hit_ops = [op for op in CMP_OPS if len(top_level_split(atom, (op,))) > 1]
        membership = bool(hit_ops) and all(op in (" in ", " !in ") for op in hit_ops)
        if membership and atom not in terms:
            terms.append(unwrap_parens(atom))
        for operand in operands:
            operand = unwrap_parens(operand)
            if len(top_level_split(operand, BOOL_OPS + CMP_OPS)) > 1:
                terms += [t for t in candidate_terms(operand) if t not in terms]
                continue
            if not is_trivial(operand) and operand not in terms and not has_binder(operand):
                terms.append(operand)
            for sub in bracketed_subterms(operand):
                if (
                    sub != operand
                    and not is_trivial(sub)
                    and sub not in terms
                    and not has_binder(sub)
                ):
                    terms.append(sub)
    return terms[:MAX_SEEDS]


def equality_atoms(expr: str) -> list[str]:
    """Top-level ``a == b`` atoms of the expression (conjuncts and implication consequents)."""
    atoms = []
    for atom in top_level_split(expr, BOOL_OPS):
        atom = unwrap_parens(atom)
        if re.search(r"\b(forall|exists)\b|::", atom):
            continue
        if len(top_level_split(atom, ("==",))) == 2 and len(top_level_split(atom, CMP_OPS)) == 2:
            atoms.append(atom)
    return atoms


# ---------------------------------------------------------------- declarations


def enclosing_decl_lines(clean: str, offset: int) -> tuple[int, int]:
    """``(first, last)`` line of the declaration containing ``offset``.

    Declarations start on their own line; a declaration extends to the line
    before the next one. Braces are not tracked because attributes and set
    displays inside specifications make brace matching unreliable.
    """
    starts = [m.start() for m in DECL_RE.finditer(clean)]
    before = [b for b in starts if b <= offset]
    if not before:
        raise ValueError(f"no enclosing declaration at offset {offset}")
    after = [b for b in starts if b > offset]
    first = clean.count("\n", 0, before[-1]) + 1
    last = clean.count("\n", 0, after[0]) if after else clean.count("\n") + 1
    return first, last

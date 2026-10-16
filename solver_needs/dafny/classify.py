"""Classify essential Dafny assertions by the probe that restores verification.

Every row of a dataset written by ``solver_needs.dafny.extract`` is an
essential assertion. Each probe replaces the whole assert statement,
by-block included, exactly as the extraction removed it, and verifies the
enclosing declaration:

* term seeds (INST): ``ghost var seedTermN := <term>;`` for each candidate
  subterm of the assertion and of the asserts inside its by-block, one at a
  time, then all together. INST-witness when a failing obligation contains
  an existential, INST-forall otherwise.
* equality seeds: ``ghost var eqTermN := (a == b);`` for each top-level
  equality; a pass is AX when one side has collection type (the seed fires
  the extensionality axiom) and INST otherwise.
* laws (AX): the stripped program verified once per sequence law appended
  to the prelude, never combined.

Every probe family runs on every row, whatever the earlier ones returned,
so that ``categories`` lists every family that restores verification and
the overlap between families can be measured; the label is the first
family of the paper's order (INST, AX) that passes, else Other. FUEL and
NLA are not probed for Dafny.

Usage::

    uv run python -m solver_needs.dafny.classify [--solver z3|cvc5] [--keys CF-0 DB-3]
        [--workers 12]
    uv run python -m solver_needs.dafny.classify --relabel   # labels from the recorded evidence

Outputs, in ``results/dafny_<solver>/``: ``rows/<key>.json`` as each row
finishes, ``probes.json`` (all rows) and ``labels.json`` (``{key: label}``).
A rerun skips rows already in ``rows/``; ``--keys`` re-probes the given rows.
"""

import argparse
import json
import re
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from solver_needs import config
from solver_needs.dafny.laws import LAWS, write_preludes
from solver_needs.dafny.shape import shape_of
from solver_needs.dafny.source import (
    candidate_terms,
    enclosing_decl_lines,
    equality_atoms,
    inner_assert_exprs,
    split_assert,
    statement_end,
    strip_comments,
)
from solver_needs.dafny.verify import DafnySettings, verify
from solver_needs.labels import CONFIGURATIONS

ORDER = ("INST", "AX")  # probe order for Dafny; the first passing family labels


class Probe:
    """The probes of one essential assertion."""

    def __init__(self, row: dict, preludes: dict[str, Path], tmp: Path, settings: DafnySettings):
        self.row = row
        self.preludes = preludes
        self.tmp = tmp
        self.settings = settings
        self.src = config.ROOT / row["source_path"]
        self.text = self.src.read_text()
        self.lines = self.text.split("\n")
        self.start = row["line"] - 1
        line = self.lines[self.start]
        self.indent = line[: len(line) - len(line.lstrip())]
        line_offset = sum(len(ln) + 1 for ln in self.lines[: self.start])
        self.stmt_begin = line_offset + self.lines[self.start].index("assert")
        self.stmt_end = statement_end(self.text, self.stmt_begin)
        self.expr, self.by_body = split_assert(self.text[self.stmt_begin : self.stmt_end])
        self.decl_lines = enclosing_decl_lines(strip_comments(self.text), self.stmt_begin)
        self.variant_decl: dict[Path, tuple[int, int]] = {}

    def variant(self, name: str, replacement: list[str]) -> Path:
        """Source with the assert statement's characters replaced by ``replacement`` lines."""
        middle = ("\n" + self.indent).join(ln.strip() for ln in replacement)
        text = self.text[: self.stmt_begin] + middle + self.text[self.stmt_end :]
        path = self.tmp / f"{self.row['key']}_{name}.dfy"
        path.write_text(text)
        # the declaration's line range on this variant (the end line shifts
        # when the replacement has a different number of lines)
        self.variant_decl[path] = enclosing_decl_lines(strip_comments(text), self.stmt_begin)
        return path

    def check(self, path: Path, prelude: Path | None = None) -> str:
        """Verify a variant, restricted to the enclosing declaration."""
        return verify(path, self.settings, prelude, filter_lines=self.variant_decl[path])[0]

    def seed_probe(self) -> dict[str, str]:
        """Term seeds, one at a time, stopping at the first pass, then all valid ones together."""
        terms = candidate_terms(self.expr)
        for inner in inner_assert_exprs(self.by_body or ""):
            terms += [t for t in candidate_terms(inner) if t not in terms]
        terms = terms[: config.MAX_SEEDS]
        outcomes: dict[str, str] = {}
        for i, term in enumerate(terms):
            outcomes[term] = self.check(
                self.variant(f"seed{i}", [f"{self.indent}ghost var seedTerm{i} := {term};"])
            )
            if outcomes[term] == "pass":
                return outcomes
        valid = [t for t, s in outcomes.items() if s != "invalid"]
        if len(valid) > 1:
            outcomes["<all>"] = self.check(
                self.variant(
                    "seedall",
                    [f"{self.indent}ghost var seedTerm{i} := {t};" for i, t in enumerate(valid)],
                )
            )
        return outcomes

    def eq_seed_probe(self) -> dict[str, str]:
        """Equality seeds for the top-level equalities, stopping at the first pass."""
        outcomes: dict[str, str] = {}
        for i, atom in enumerate(equality_atoms(self.expr)[: config.MAX_EQUALITY_SEEDS]):
            outcomes[atom] = self.check(
                self.variant(f"eq{i}", [f"{self.indent}ghost var eqTerm{i} := ({atom});"])
            )
            if outcomes[atom] == "pass":
                break
        return outcomes

    def law_probe(self) -> list[str]:
        """Every sequence law under which the stripped program verifies."""
        removed = self.variant("removed", [])
        return [name for name in LAWS if self.check(removed, self.preludes[name]) == "pass"]

    def run(self) -> dict:
        """Run every probe and decide the label."""
        result: dict = {
            "key": self.row["key"],
            "expr": self.expr,
            "has_by_block": self.by_body is not None,
            "decl_lines": list(self.decl_lines),
        }
        result["seeds"] = self.seed_probe()
        result["eq_seeds"] = self.eq_seed_probe()
        result["prelude_axioms"] = self.law_probe()
        result["shape"] = shape_of(self.row["source_path"], self.row["line"], self.expr)
        result["label"] = self.decide(result)
        return result

    @staticmethod
    def categories(r: dict) -> list[str]:
        """Every family whose probe restores verification, from the stored evidence."""
        eq_pass = "pass" in r["eq_seeds"].values()
        found = []
        if "pass" in r["seeds"].values() or (eq_pass and not r["shape"]["collection_eq"]):
            found.append("INST")
        if (eq_pass and r["shape"]["collection_eq"]) or r["prelude_axioms"]:
            found.append("AX")
        return found

    def decide(self, r: dict) -> str:
        """The first family of the paper's order whose probe passed, else Other."""
        r["categories"] = self.categories(r)
        for category in ORDER:
            if category in r["categories"]:
                return self.inst_label(r) if category == "INST" else category
        return "Other"

    def inst_label(self, r: dict) -> str:
        """INST-witness if a failing obligation asks for a witness, else INST-forall."""
        for error in self.row.get("removal_errors") or []:
            if self.goal_is_existential(error):
                r["witness_error_line"] = error.get("line")
                return "INST-witness"
        r["witness_error_line"] = None
        return "INST-forall"

    def goal_is_existential(self, error: dict) -> bool:
        """Does the obligation that failed on removal contain an existential?"""
        if not error:
            return False
        if "such-that" in error.get("message", ""):
            return True
        candidates = [error.get("related_line"), error.get("line"), *error.get("related_lines", [])]
        texts = [self.lines[ln - 1] for ln in candidates if ln and 0 < ln <= len(self.lines)]
        joined = " ".join(texts)
        if re.search(r"\bexists\b", joined):
            return True
        return any(
            self.declaration_has_exists(name)
            for name in re.findall(r"\b([A-Za-z_]\w*)\s*\(", joined)
        )

    def declaration_has_exists(self, name: str) -> bool:
        """True if predicate ``name``'s body or method ``name``'s requires contains an exists."""
        decl = re.search(
            rf"\b(ghost\s+)?(predicate|function)(\s+method)?\s+{re.escape(name)}\b.*?\n\}}",
            self.text,
            re.S,
        )
        if decl and re.search(r"\bexists\b", decl.group(0)):
            return True
        call = re.search(rf"\b(method|lemma)\s+{re.escape(name)}\b(.*?)\n\s*\{{", self.text, re.S)
        return bool(call and re.search(r"\brequires\b[^\n]*\bexists\b", call.group(2)))


# ---------------------------------------------------------------- driver


def cached_rows(results_dir: Path, keys: list[str]) -> dict[str, dict]:
    """Per-row results already on disk, in dataset order."""
    out = {}
    for key in keys:
        path = results_dir / "rows" / f"{key}.json"
        if path.exists():
            out[key] = json.loads(path.read_text())
    return out


def write_outputs(results: list[dict], results_dir: Path, toolchain: dict) -> None:
    """Write ``probes.json`` and ``labels.json``."""
    (results_dir / "probes.json").write_text(json.dumps(results, indent=1) + "\n")
    labels = {
        "probes": "term seeds, equality seeds, sequence laws (solver_needs.dafny.classify)",
        "order": list(ORDER),
        "toolchain": toolchain,
        "labels": {r["key"]: r["label"] for r in results},
    }
    (results_dir / "labels.json").write_text(json.dumps(labels, indent=1) + "\n")


def relabel(dataset: dict, results_dir: Path, settings: DafnySettings) -> None:
    """Recompute every label from the stored probe evidence (no Dafny runs)."""
    rows = {a["key"]: a for a in dataset["assertions"]}
    cached = cached_rows(results_dir, list(rows))
    with tempfile.TemporaryDirectory(prefix="relabel_") as tmpdir:
        for key, r in cached.items():
            r["label"] = Probe(rows[key], {}, Path(tmpdir), settings).decide(r)
            (results_dir / "rows" / f"{key}.json").write_text(json.dumps(r, indent=1) + "\n")
    write_outputs(list(cached.values()), results_dir, dataset["toolchain"])


def main() -> int:
    """Command line entry point."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--solver", choices=config.SOLVERS, default="z3")
    parser.add_argument("--dataset", type=Path, help="default: the recorded dataset of the solver")
    parser.add_argument("--results-dir", type=Path, help="default: results/dafny_<solver>")
    parser.add_argument("--keys", nargs="*", help="re-probe only these rows (cached or not)")
    parser.add_argument("--workers", type=int, default=12)
    parser.add_argument(
        "--relabel", action="store_true", help="labels from the stored rows, no Dafny runs"
    )
    args = parser.parse_args()
    configuration = CONFIGURATIONS[f"dafny_{args.solver}"]
    results_dir = args.results_dir or configuration["results"]
    dataset = json.loads((args.dataset or configuration["dataset"]).read_text())
    settings = DafnySettings.for_solver(args.solver)
    (results_dir / "rows").mkdir(parents=True, exist_ok=True)
    if args.relabel:
        relabel(dataset, results_dir, settings)
        return 0

    rows = dataset["assertions"]
    keys = [a["key"] for a in rows]
    cached = cached_rows(results_dir, keys)
    if args.keys:
        todo = [a for a in rows if a["key"] in set(args.keys)]
    else:
        todo = [a for a in rows if a["key"] not in cached]
    print(f"{len(rows)} rows, {len(cached)} cached, {len(todo)} to probe", flush=True)

    preludes = write_preludes()
    with tempfile.TemporaryDirectory(prefix="classify_") as tmpdir:

        def one(row: dict) -> None:
            try:
                res = Probe(row, preludes, Path(tmpdir), settings).run()
            except Exception as exc:  # noqa: BLE001 - record and continue, do not lose the batch
                res = {"key": row["key"], "label": "ERROR", "error": f"{type(exc).__name__}: {exc}"}
            (results_dir / "rows" / f"{row['key']}.json").write_text(
                json.dumps(res, indent=1) + "\n"
            )
            print(f"{res['key']:8s} {res['label']}", flush=True)

        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            list(pool.map(one, todo))

    write_outputs(list(cached_rows(results_dir, keys).values()), results_dir, settings.describe())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

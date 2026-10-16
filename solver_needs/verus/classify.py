"""Classify essential Verus assertions by the probe that restores verification.

Verus counterpart of ``solver_needs.dafny.classify``. Every variant
replaces the whole assert statement, by-block included, exactly as the
extraction removed it, and the whole file is verified:

* FUEL: ``reveal_with_fuel(f, 20);`` for each recursive spec fn the
  assertion mentions, one at a time, then all together. Runs first
  because in Verus a fresh call in a seed term carries fresh fuel and
  would pass for the wrong reason.
* INST: ``let ghost seed_termN = <term>;`` per candidate subterm of the
  assertion and of the asserts inside its by-block, then all together.
  For ``assert forall`` statements, whose subterms all mention the bound
  variable, the statement is instead replaced by ``assert forall ... by {}``
  with an empty body (the *bridge*); a pass means only the skolemization
  bridge was missing and is INST-forall.
* equality seeds: ``let ghost eq_termN = (a =~= b);`` per top-level
  equality; a pass is AX on a collection equality and INST otherwise.
* AX: the stripped program with one sequence law injected as a
  ``broadcast proof fn``, never combined.
* NLA (Z3 only): the stripped program with ``--smt-option smt.arith.nl=true``.

Every probe family runs on every row and ``categories`` lists all that
pass; the label is the first family of the paper's order (FUEL, INST, AX,
NLA) that passes, else Other.

Usage::

    uv run python -m solver_needs.verus.classify [--solver z3|cvc5] [--keys V-0 VB-8] [--workers 6]
    uv run python -m solver_needs.verus.classify --relabel   # labels from the recorded evidence

Outputs, in ``results/verus_<solver>/``: ``rows/<key>.json`` as each row
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
from solver_needs.labels import CONFIGURATIONS
from solver_needs.verus.laws import LAWS, with_law
from solver_needs.verus.source import (
    candidate_terms,
    equality_atoms,
    in_proof_context,
    inner_assert_exprs,
    mask_generics,
    recursive_spec_fns,
    shape_from_text,
    split_assert,
    statement_end,
    unmask,
)
from solver_needs.verus.verify import VerusSettings, probe_status, run

ORDER = ("FUEL", "INST", "AX", "NLA")  # probe order for Verus; the first passing family labels


class Probe:
    """The probes of one essential assertion."""

    def __init__(self, row: dict, tmp: Path, settings: VerusSettings):
        self.row = row
        self.tmp = tmp
        self.settings = settings
        self.text = (config.ROOT / row["source_path"]).read_text()
        self.lines = self.text.split("\n")
        self.start = row["line"] - 1
        line = self.lines[self.start]
        self.indent = line[: len(line) - len(line.lstrip())]
        line_offset = sum(len(ln) + 1 for ln in self.lines[: self.start])
        self.stmt_begin = line_offset + self.lines[self.start].index("assert")
        self.stmt_end = statement_end(self.text, self.stmt_begin)
        parsed = split_assert(self.text[self.stmt_begin : self.stmt_end])
        self.kind = parsed["kind"]
        self.expr = parsed["expr"]
        self.by_body = parsed["by_body"]
        self.tactic = parsed["tactic"]
        self.proof_ctx = in_proof_context(self.text, self.stmt_begin)

    def variant(self, name: str, replacement: list[str], law: str | None = None) -> Path:
        """Source with the statement replaced by ``replacement`` lines, plus an optional law."""
        middle = ("\n" + self.indent).join(ln.strip() for ln in replacement)
        text = self.text[: self.stmt_begin] + middle + self.text[self.stmt_end :]
        if law is not None:
            text = with_law(text, law)
        path = self.tmp / f"{self.row['key']}_{name}.rs"
        path.write_text(text)
        return path

    def check(self, path: Path, extra: tuple[str, ...] = ()) -> str:
        """Verify a variant; pass | fail | timeout | invalid."""
        return probe_status(run(path, self.settings, extra=extra))[0]

    def proof_stmt(self, name: str, stmts: list[str]) -> str:
        """Verify ``stmts`` in proof context, wrapping them in ``proof { }`` inside exec code."""
        if self.proof_ctx:
            return self.check(self.variant(name, ["{", *stmts, "}"]))
        return self.check(self.variant(name, ["proof {", *stmts, "}"]))

    def fuel_probe(self) -> dict[str, str]:
        """``reveal_with_fuel`` per recursive spec fn the assertion mentions, then all together."""
        recursive = recursive_spec_fns(self.text)
        mentioned = [
            f for f in dict.fromkeys(re.findall(r"\b(\w+)\s*\(", self.expr)) if f in recursive
        ]
        outcomes: dict[str, str] = {}
        for f in mentioned:
            outcomes[f] = self.proof_stmt(
                f"fuel_{f}", [f"reveal_with_fuel({f}, {config.VERUS_FUEL});"]
            )
            if outcomes[f] == "pass":
                return outcomes
        if len(mentioned) > 1:
            outcomes["<all>"] = self.proof_stmt(
                "fuel_all", [f"reveal_with_fuel({f}, {config.VERUS_FUEL});" for f in mentioned]
            )
        return outcomes

    def seed_probe(self) -> dict[str, str]:
        """Term seeds of the assertion and of the asserts inside its by-block, then all together."""
        masked, table = mask_generics(self.expr)
        outer = candidate_terms(masked)
        inner: list[str] = []
        for expr in inner_assert_exprs(self.by_body or ""):
            inner_masked, inner_table = mask_generics(expr)
            table.update(inner_table)
            inner += [t for t in candidate_terms(inner_masked) if t not in outer + inner]
        terms = [unmask(t, table) for t in outer + inner][: config.MAX_SEEDS]
        outcomes: dict[str, str] = {}
        for i, term in enumerate(terms):
            outcomes[term] = self.seed_variant(f"seed{i}", [(i, term)])
            if outcomes[term] == "pass":
                return outcomes
        valid = [(i, t) for i, t in enumerate(terms) if outcomes[t] != "invalid"]
        if len(valid) > 1:
            outcomes["<all>"] = self.seed_variant("seedall", valid)
        return outcomes

    def seed_variant(self, name: str, seeds: list[tuple[int, str]]) -> str:
        """Verify the statement replaced by ``let ghost seed_termN = t;`` declarations."""
        return self.check(self.variant(name, [f"let ghost seed_term{i} = {t};" for i, t in seeds]))

    def eq_seed_probe(self) -> dict[str, str]:
        """Equality seeds for the top-level equalities, stopping at the first pass."""
        masked, table = mask_generics(self.expr)
        outcomes: dict[str, str] = {}
        for i, (_op, a, b) in enumerate(equality_atoms(masked)[: config.MAX_EQUALITY_SEEDS]):
            atom = unmask(f"{a} =~= {b}", table)
            outcomes[atom] = self.check(
                self.variant(f"eq{i}", [f"let ghost eq_term{i} = ({atom});"])
            )
            if outcomes[atom] == "pass":
                break
        return outcomes

    def nla_probe(self) -> str:
        """The stripped program with Z3's nonlinear arithmetic re-enabled; ``n/a`` under cvc5."""
        if self.settings.solver == "cvc5":
            return "n/a"
        return self.check(self.variant("removed", []), ("--smt-option", "smt.arith.nl=true"))

    def run(self) -> dict:
        """Run every probe and decide the label."""
        result: dict = {
            "key": self.row["key"],
            "kind": self.kind,
            "expr": self.expr,
            "tactic": self.tactic,
            "has_by_block": self.by_body is not None,
            "proof_context": self.proof_ctx,
        }
        result["fuel"] = self.fuel_probe()
        result["bridge"] = None
        result["seeds"] = {}
        result["eq_seeds"] = {}
        if self.kind == "forall":
            result["bridge"] = self.check(self.variant("bridge", [f"assert {self.expr} by {{}}"]))
        else:
            result["seeds"] = self.seed_probe()
            result["eq_seeds"] = self.eq_seed_probe()
        result["axioms"] = [
            name for name in LAWS if self.check(self.variant(f"ax_{name}", [], law=name)) == "pass"
        ]
        result["nla"] = self.nla_probe()
        result["shape"] = shape_from_text(self.expr, self.tactic)
        result["label"] = self.decide(result)
        return result

    @staticmethod
    def categories(r: dict) -> list[str]:
        """Every family whose probe restores verification, from the stored evidence."""
        eq_pass = "pass" in r["eq_seeds"].values()
        found = []
        if "pass" in r["fuel"].values():
            found.append("FUEL")
        if (
            r.get("bridge") == "pass"
            or "pass" in r["seeds"].values()
            or (eq_pass and not r["shape"]["collection_eq"])
        ):
            found.append("INST")
        if (eq_pass and r["shape"]["collection_eq"]) or r["axioms"]:
            found.append("AX")
        if r["nla"] == "pass":
            found.append("NLA")
        return found

    def decide(self, r: dict) -> str:
        """The first family of the paper's order whose probe passed, else Other."""
        r["categories"] = self.categories(r)
        for category in ORDER:
            if category not in r["categories"]:
                continue
            if category != "INST":
                return category
            if r.get("bridge") == "pass" and "pass" not in r["seeds"].values():
                return "INST-forall"
            return self.inst_label(self.row.get("removal_error") or {})
        return "Other"

    def inst_label(self, error: dict) -> str:
        """INST-witness if the failing obligation contains an existential, else INST-forall."""
        return "INST-witness" if self.goal_is_existential(error) else "INST-forall"

    def goal_is_existential(self, error: dict) -> bool:
        """Does the failing obligation, or a spec/proof fn it calls, contain ``exists``?"""
        ln = error.get("line")
        if not ln or not 0 < ln <= len(self.lines):
            return False
        goal = " ".join(self.lines[ln - 1 : ln + 2])
        if re.search(r"\bexists\s*\|", goal):
            return True
        for name in re.findall(r"\b([A-Za-z_]\w*)\s*\(", goal):
            decl = re.search(rf"\b(spec|proof)\s+fn\s+{re.escape(name)}\b.*?\n\}}", self.text, re.S)
            if decl and re.search(r"\bexists\s*\|", decl.group(0)):
                return True
        return False


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
    results_dir.mkdir(exist_ok=True)
    (results_dir / "probes.json").write_text(json.dumps(results, indent=1) + "\n")
    labels = {
        "probes": "fuel, bridge, term seeds, equality seeds, sequence laws, nla "
        "(solver_needs.verus.classify)",
        "order": list(ORDER),
        "toolchain": toolchain,
        "labels": {r["key"]: r["label"] for r in results},
    }
    (results_dir / "labels.json").write_text(json.dumps(labels, indent=1) + "\n")


def relabel(dataset: dict, results_dir: Path, settings: VerusSettings) -> None:
    """Recompute every label from the stored probe evidence (no Verus runs)."""
    rows = {a["key"]: a for a in dataset["assertions"]}
    cached = cached_rows(results_dir, list(rows))
    with tempfile.TemporaryDirectory(prefix="verus_relabel_") as tmpdir:
        for key, r in cached.items():
            r["label"] = Probe(rows[key], Path(tmpdir), settings).decide(r)
            (results_dir / "rows" / f"{key}.json").write_text(json.dumps(r, indent=1) + "\n")
    write_outputs(list(cached.values()), results_dir, dataset["toolchain"])


def main() -> int:
    """Command line entry point."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--solver", choices=config.SOLVERS, default="z3")
    parser.add_argument("--dataset", type=Path, help="default: the recorded dataset of the solver")
    parser.add_argument("--results-dir", type=Path, help="default: results/verus_<solver>")
    parser.add_argument("--keys", nargs="*", help="re-probe only these rows (cached or not)")
    parser.add_argument("--workers", type=int, default=6)
    parser.add_argument(
        "--relabel", action="store_true", help="labels from the stored rows, no Verus runs"
    )
    args = parser.parse_args()
    configuration = CONFIGURATIONS[f"verus_{args.solver}"]
    results_dir = args.results_dir or configuration["results"]
    dataset = json.loads((args.dataset or configuration["dataset"]).read_text())
    settings = VerusSettings(args.solver)
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

    with tempfile.TemporaryDirectory(prefix="verus_classify_") as tmpdir:

        def one(row: dict) -> None:
            try:
                res = Probe(row, Path(tmpdir), settings).run()
            except Exception as exc:  # noqa: BLE001 - record and continue, do not lose the batch
                res = {"key": row["key"], "label": "ERROR", "error": f"{type(exc).__name__}: {exc}"}
            (results_dir / "rows" / f"{row['key']}.json").write_text(
                json.dumps(res, indent=1) + "\n"
            )
            print(f"{res['key']:6s} {res['label']}", flush=True)

        with ThreadPoolExecutor(max_workers=args.workers) as pool:
            list(pool.map(one, todo))

    write_outputs(list(cached_rows(results_dir, keys).values()), results_dir, settings.describe())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

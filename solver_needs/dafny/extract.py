"""Extract the essential assertions of the Dafny corpora.

Every program whose baseline verifies fully is probed: each unlabelled
``assert`` statement in statement position is removed on its own, by
character range, and the enclosing declaration is re-verified. A removal
that fails is re-verified under Boogie's second random seed and with the
statement replaced by the inert ``ghost var placeboTerm := 0;``. The
assertion is essential only if all three runs fail (an error, an exhausted
budget, or the wall-clock safety net). Labelled assertions (``assert L: E``)
are never candidates: removing one breaks a later ``reveal L`` and says
nothing about the solver.

Programs whose baseline does not verify fully are recorded with their
status and skipped. Errors reported outside the enclosing declaration are
counted in ``other_errors`` but ignored: removing an assert cannot change
the verification of another declaration.

Keys are carried over from the previous dataset when source, line or text
match; new assertions continue the numbering and retired keys are never
reused, so keys stay stable across re-extractions.

Usage::

    uv run python -m solver_needs.dafny.extract [--solver z3|cvc5] [--programs P ...]
        [--workers 12] [--out data/essential/essential_dafny_z3.json]

Per-program results are cached under ``work/extract_<solver>/``; delete a
file there to re-probe that program.
"""

import argparse
import json
import re
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from solver_needs import config
from solver_needs.corpora import KEY_PREFIX, dafny_sources, relative, select_programs
from solver_needs.dafny.source import (
    assert_statements,
    enclosing_decl_lines,
    is_labelled,
    strip_comments,
)
from solver_needs.dafny.verify import (
    DafnySettings,
    all_errors,
    errors_to_source_lines,
    status_within,
    verify,
)
from solver_needs.labels import CONFIGURATIONS

FAILING = ("fail", "timeout", "wall-timeout")  # removal outcomes that keep an assertion essential
ROW_FIELDS = (
    "key",
    "corpus",
    "problem",
    "source_path",
    "line",
    "end_line",
    "text",
    "removal",
    "removal_confirm",
    "removal_seed2",
    "placebo",
    "removal_error",
    "removal_errors",
    "other_errors",
    "new_key",
)


def check_variant(
    variant_text: str,
    variant: Path,
    span: tuple[int, int],
    settings: DafnySettings,
    resource_limit: int | None = None,
    seed: int | None = None,
) -> tuple[str, int, str, tuple[int, int]]:
    """Verify a variant restricted to the declaration enclosing ``span``.

    Returns ``(status, errors elsewhere, output, declaration line span)``.
    """
    variant.write_text(variant_text)
    decl = enclosing_decl_lines(strip_comments(variant_text), span[0])
    status, out = verify(
        variant, settings, resource_limit=resource_limit, seed=seed, filter_lines=decl
    )
    status, other = status_within(status, out, decl)
    return status, other, out, decl


def probe_removal(
    path: Path, span: tuple[int, int], variant: Path, settings: DafnySettings
) -> dict:
    """Removal outcome and, when it fails, the two stability checks.

    ``removal_seed2`` repeats the removal under Boogie's second random seed
    and ``placebo`` replaces the statement by an inert ghost declaration; an
    exhausted budget on removal is confirmed once at twice the limit, for
    the record (``removal_confirm``).
    """
    text = path.read_text()
    removed = text[: span[0]] + text[span[1] :]
    status, other, out, decl = check_variant(removed, variant, span, settings)
    start_line = text.count("\n", 0, span[0]) + 1
    removed_newlines = text.count("\n", span[0], span[1])
    inside = [e for e in all_errors(out) if decl[0] <= e["line"] <= decl[1]]
    errors = errors_to_source_lines(inside, removed_newlines, start_line)
    result = {
        "removal": status,
        "removal_confirm": None,
        "removal_seed2": None,
        "placebo": None,
        "other_errors": other,
        "removal_error": errors[0] if errors else {},
        "removal_errors": errors,
    }
    if status not in FAILING:
        return result
    if status == "timeout":
        result["removal_confirm"] = check_variant(
            removed, variant, span, settings, resource_limit=2 * settings.resource_limit
        )[0]
    result["removal_seed2"] = check_variant(
        removed, variant, span, settings, seed=config.DAFNY_SECOND_SEED
    )[0]
    placebo = text[: span[0]] + "ghost var placeboTerm := 0;" + text[span[1] :]
    result["placebo"] = check_variant(
        placebo, variant.with_name(variant.stem + "_placebo.dfy"), span, settings
    )[0]
    return result


def is_essential(outcome: dict) -> bool:
    """Essential: the removal, its second-seed rerun and the placebo all fail."""
    return (
        outcome["removal"] in FAILING
        and outcome["removal_seed2"] in FAILING
        and outcome["placebo"] in FAILING
    )


def verify_baseline(path: Path, settings: DafnySettings) -> tuple[str, str | None]:
    """Baseline status, plus the status at twice the limit when out of resource."""
    status, _ = verify(path, settings)
    confirm = None
    if status == "timeout":
        confirm = verify(path, settings, resource_limit=2 * settings.resource_limit)[0]
    return status, confirm


def assertion_row(text: str, span: tuple[int, int], outcome: dict) -> dict:
    """The dataset row of one probed assertion."""
    begin, end = span
    return {
        "line": text.count("\n", 0, begin) + 1,
        "end_line": text.count("\n", 0, end) + 1,
        "text": re.sub(r"\s+", " ", text[begin:end]).strip(),
        **outcome,
        "essential": is_essential(outcome),
    }


def removal_tasks(record: dict, path: Path, tmp: Path) -> list[tuple[tuple[int, int], Path]]:
    """The ``(span, variant file)`` of every unlabelled assert of a passing program."""
    text = path.read_text()
    tasks = []
    for idx, span in enumerate(assert_statements(text)):
        if is_labelled(text[span[0] : span[1]]):
            record["asserts_labelled"] += 1
            continue
        tasks.append((span, tmp / f"{record['corpus']}_{record['problem'][:60]}_{idx}.dfy"))
    return tasks


def probe_programs(
    sources: list[tuple[str, str, Path]],
    tmp: Path,
    settings: DafnySettings,
    workers: int,
    cache_dir: Path,
) -> list[dict]:
    """Baseline every program, then probe every unlabelled assertion of the passing ones.

    Finished programs are cached in ``cache_dir`` and skipped on rerun.
    """
    cache_dir.mkdir(parents=True, exist_ok=True)
    records: dict[str, dict] = {}
    todo = []
    for corpus, problem, path in sources:
        cached = cache_dir / f"{corpus}_{problem}.json"
        if cached.exists():
            records[problem] = json.loads(cached.read_text())
        else:
            todo.append((corpus, problem, path))
    print(f"{len(records)} programs cached, {len(todo)} to probe", flush=True)

    with ThreadPoolExecutor(max_workers=workers) as pool:
        baselines = list(pool.map(lambda item: verify_baseline(item[2], settings), todo))
    tasks = []
    for (corpus, problem, path), (baseline, confirm) in zip(todo, baselines, strict=True):
        records[problem] = {
            "corpus": corpus,
            "problem": problem,
            "source_path": relative(path),
            "baseline": baseline,
            "baseline_confirm": confirm,
            "asserts_labelled": 0,
            "assertions": [],
        }
        if baseline == "pass":
            tasks += [
                (problem, path, span, variant)
                for span, variant in removal_tasks(records[problem], path, tmp)
            ]
    print(f"{len(tasks)} removal probes", flush=True)

    def probe(task: tuple[str, Path, tuple[int, int], Path]) -> None:
        problem, path, span, variant = task
        row = assertion_row(path.read_text(), span, probe_removal(path, span, variant, settings))
        rec = records[problem]
        rec["assertions"].append(row)
        rec["assertions"].sort(key=lambda a: a["line"])

    with ThreadPoolExecutor(max_workers=workers) as pool:
        list(pool.map(probe, tasks))
    for corpus, problem, _ in todo:
        rec = records[problem]
        (cache_dir / f"{corpus}_{problem}.json").write_text(json.dumps(rec, indent=1))
        n_ess = sum(a["essential"] for a in rec["assertions"])
        print(
            f"{rec['corpus']} {rec['problem'][:50]:50s} baseline={rec['baseline']:7s} "
            f"asserts={len(rec['assertions']):3d} essential={n_ess} "
            f"labelled={rec['asserts_labelled']}",
            flush=True,
        )
    return [records[problem] for _, problem, _ in sources]


def carry_over_keys(rows: list[dict], previous: list[dict]) -> None:
    """Assign keys: the key of the same assertion in ``previous``, else a fresh number.

    An assertion is the same when its source and line, or its source and
    text, match; fresh numbers continue above every key ever used in the
    corpus, so retired keys are never reused.
    """
    by_loc = {(a["source_path"], a["line"]): a["key"] for a in previous}
    by_text = {(a["source_path"], re.sub(r"\s+", "", a["text"])): a["key"] for a in previous}
    next_idx = {
        c: 1 + max((int(a["key"].split("-")[1]) for a in previous if a["corpus"] == c), default=-1)
        for c in KEY_PREFIX
    }
    used: set[str] = set()
    for row in rows:
        key = by_loc.get((row["source_path"], row["line"])) or by_text.get(
            (row["source_path"], re.sub(r"\s+", "", row["text"]))
        )
        if key is None or key in used:
            key = f"{KEY_PREFIX[row['corpus']]}-{next_idx[row['corpus']]}"
            next_idx[row["corpus"]] += 1
        used.add(key)
        row["key"] = key
        row["new_key"] = key not in {a["key"] for a in previous}


def build_dataset(records: list[dict], previous: list[dict], settings: DafnySettings) -> dict:
    """The dataset of every essential assertion, with per-program and count blocks."""
    rows = [
        {"corpus": r["corpus"], "problem": r["problem"], "source_path": r["source_path"], **a}
        for r in records
        for a in r["assertions"]
        if a["essential"]
    ]
    carry_over_keys(rows, previous)
    ordered = [{k: row.get(k) for k in ROW_FIELDS} for row in rows]
    passing = [r for r in records if r["baseline"] == "pass"]
    statuses = ("pass", "fail", "timeout", "invalid", "wall-timeout")
    return {
        "description": (
            "Essential Dafny assertions: every unlabelled assert of a "
            "program whose baseline verifies fully is removed by character range; it is "
            "essential when the enclosing declaration then fails (removal: fail, timeout = "
            "budget exhausted, wall-timeout = safety net), still fails under a second random "
            "seed (removal_seed2) and still fails with the inert 'ghost var placeboTerm := 0;' "
            "in its place (placebo). removal_errors are the failing obligations on removal, "
            "in source line numbers."
        ),
        "toolchain": settings.describe(),
        "programs": [
            {
                k: r.get(k)
                for k in ("corpus", "problem", "source_path", "baseline", "baseline_confirm")
            }
            | {"asserts": len(r["assertions"]), "asserts_labelled": r["asserts_labelled"]}
            for r in records
        ],
        "counts": {
            "programs": len(records),
            "baseline": {s: sum(r["baseline"] == s for r in records) for s in statuses},
            "asserts_labelled": sum(r["asserts_labelled"] for r in passing),
            "asserts_probed": sum(len(r["assertions"]) for r in passing),
            "removal_fails": sum(a["removal"] in FAILING for r in passing for a in r["assertions"]),
            "unstable": sum(
                a["removal"] in FAILING and not a["essential"]
                for r in passing
                for a in r["assertions"]
            ),
            "essential": len(ordered),
            "removal": {s: sum(r["removal"] == s for r in ordered) for s in FAILING},
            "carried_over": sum(not r["new_key"] for r in ordered),
            "new": sum(1 for r in ordered if r["new_key"]),
            **{c: sum(r["corpus"] == c for r in ordered) for c in ("CF-D", "DB")},
        },
        "assertions": ordered,
    }


def main() -> int:
    """Command line entry point."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--solver", choices=config.SOLVERS, default="z3")
    parser.add_argument(
        "--programs", nargs="*", help="only these problems (default: every program)"
    )
    parser.add_argument("--workers", type=int, default=12)
    parser.add_argument("--out", type=Path, help="output dataset (default: the recorded one)")
    parser.add_argument(
        "--cache-dir", type=Path, help="per-program cache (default work/extract_<solver>)"
    )
    parser.add_argument(
        "--previous",
        type=Path,
        help="dataset whose keys are carried over (default: the recorded one; skipped when absent)",
    )
    args = parser.parse_args()
    recorded = CONFIGURATIONS[f"dafny_{args.solver}"]["dataset"]
    out_path = args.out or recorded
    previous_path = args.previous or recorded
    cache_dir = args.cache_dir or config.WORK / f"extract_{args.solver}"
    settings = DafnySettings.for_solver(args.solver)

    sources = select_programs(dafny_sources(), args.programs)
    print(f"{len(sources)} programs")
    with tempfile.TemporaryDirectory(prefix="extract_") as tmpdir:
        records = probe_programs(sources, Path(tmpdir), settings, args.workers, cache_dir)
    previous = json.loads(previous_path.read_text())["assertions"] if previous_path.exists() else []
    dataset = build_dataset(records, previous, settings)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(dataset, indent=1) + "\n")
    print(json.dumps(dataset["counts"], indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

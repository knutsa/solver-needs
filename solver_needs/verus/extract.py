"""Extract the essential assertions of the Verus corpora.

Verus counterpart of ``solver_needs.dafny.extract``. Every file whose
baseline verifies fully under ``--rlimit 10`` is probed: each ghost
``assert`` statement is removed on its own (by character range) and the
enclosing function is re-verified. When that fails, the statement is
replaced by the inert ``let ghost placebo_term = 0int;``. The assertion is
essential only if both runs fail (an error, an exhausted rlimit re-checked
once at ``--rlimit 20`` in ``removal_confirm``, or the wall-clock safety
net). A removal that no longer compiles is not essential: the assertion
was referenced structurally, not needed by the solver.

Files whose baseline does not verify fully are recorded with their status
and skipped. Errors in other functions are counted in ``other_errors`` and
ignored. The Rust macro ``assert!(...)`` is never a candidate.

Keys are carried over from the previous dataset when problem and line, or
problem and text, match; new assertions continue the numbering and retired
keys are never reused.

Usage::

    uv run python -m solver_needs.verus.extract [--solver z3|cvc5] [--programs P ...]
        [--workers 6] [--out data/essential/essential_verus_z3.json]

Per-file results are cached under ``work/verus_extract_<solver>/``; delete
a file there to re-probe that program.
"""

import argparse
import json
import re
import tempfile
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from solver_needs import config
from solver_needs.corpora import KEY_PREFIX, relative, select_programs, verus_sources
from solver_needs.dafny.source import strip_comments
from solver_needs.dafny.verify import errors_to_source_lines
from solver_needs.labels import CONFIGURATIONS
from solver_needs.verus.source import assert_statements, enclosing_fn_lines
from solver_needs.verus.verify import (
    VerusSettings,
    baseline_status,
    error_lines,
    file_status,
    run,
    status_within,
)

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
    "placebo",
    "removal_error",
    "removal_errors",
    "other_errors",
    "new_key",
)


def verify_file(
    path: Path, settings: VerusSettings, rlimit: float = config.VERUS_RLIMIT
) -> tuple[str, str]:
    """``(status, output)`` of a whole-file run: pass | fail | invalid | wall-timeout."""
    output = run(path, settings, rlimit, wall_timeout=config.VERUS_EXTRACT_WALL_TIMEOUT)
    return file_status(output), output or ""


def check_variant(
    variant_text: str,
    variant: Path,
    span: tuple[int, int],
    settings: VerusSettings,
    rlimit: float = config.VERUS_RLIMIT,
) -> tuple[str, int, str, tuple[int, int]]:
    """Verify a variant restricted to the function enclosing ``span``.

    Returns ``(status, errors elsewhere, output, function line span)``.
    """
    variant.write_text(variant_text)
    fn_span = enclosing_fn_lines(strip_comments(variant_text), span[0])
    status, out = verify_file(variant, settings, rlimit)
    status, other = status_within(status, out, fn_span)
    return status, other, out, fn_span


def probe_removal(text: str, span: tuple[int, int], variant: Path, settings: VerusSettings) -> dict:
    """Removal outcome and, when it fails, the placebo stability check."""
    removed = text[: span[0]] + text[span[1] :]
    status, other, out, fn_span = check_variant(removed, variant, span, settings)
    start_line = text.count("\n", 0, span[0]) + 1
    removed_newlines = text.count("\n", span[0], span[1])
    inside = [
        {"line": line, "message": message}
        for line, message in error_lines(out)
        if fn_span[0] <= line <= fn_span[1]
    ]
    errors = errors_to_source_lines(inside, removed_newlines, start_line)
    result = {
        "removal": status,
        "removal_confirm": None,
        "placebo": None,
        "other_errors": other,
        "removal_error": errors[0] if errors else {},
        "removal_errors": errors,
    }
    if status not in FAILING:
        return result
    if status == "timeout":
        result["removal_confirm"] = check_variant(
            removed, variant, span, settings, rlimit=config.VERUS_CONFIRM_RLIMIT
        )[0]
    placebo = text[: span[0]] + "let ghost placebo_term = 0int;" + text[span[1] :]
    result["placebo"] = check_variant(
        placebo, variant.with_name(variant.stem + "_placebo.rs"), span, settings
    )[0]
    return result


def is_essential(outcome: dict) -> bool:
    """Essential: the removal and the placebo both fail."""
    return outcome["removal"] in FAILING and outcome["placebo"] in FAILING


def probe_program(
    corpus: str, problem: str, path: Path, tmp: Path, settings: VerusSettings
) -> dict:
    """Baseline one file, then probe every ghost assert if the baseline passes."""
    text = path.read_text()
    status, out = verify_file(path, settings)
    baseline = baseline_status(status, out)
    confirm = None
    if baseline == "timeout":
        confirm = baseline_status(*verify_file(path, settings, rlimit=config.VERUS_CONFIRM_RLIMIT))
    record = {
        "corpus": corpus,
        "problem": problem,
        "source_path": relative(path),
        "baseline": baseline,
        "baseline_confirm": confirm,
        "assertions": [],
    }
    if baseline == "pass":
        for i, span in enumerate(assert_statements(text)):
            variant = tmp / f"{corpus}_{problem.replace('/', '__')}_{i}.rs"
            outcome = probe_removal(text, span, variant, settings)
            record["assertions"].append(
                {
                    "line": text.count("\n", 0, span[0]) + 1,
                    "end_line": text.count("\n", 0, span[1] - 1) + 1,
                    "text": text[span[0] : span[1]].strip(),
                    **outcome,
                    "essential": is_essential(outcome),
                }
            )
    return record


def probe_programs(
    sources: list[tuple[str, str, Path]],
    tmp: Path,
    settings: VerusSettings,
    workers: int,
    cache_dir: Path,
) -> list[dict]:
    """Probe every file, reusing the per-file records cached in ``cache_dir``."""
    cache_dir.mkdir(parents=True, exist_ok=True)

    def one(source: tuple[str, str, Path]) -> dict:
        corpus, problem, path = source
        cache = cache_dir / f"{corpus}_{problem.replace('/', '__')}.json"
        if cache.exists():
            rec = json.loads(cache.read_text())
        else:
            rec = probe_program(corpus, problem, path, tmp, settings)
            cache.write_text(json.dumps(rec, indent=1) + "\n")
        essential = sum(a["essential"] for a in rec["assertions"])
        print(
            f"{corpus} {problem}: baseline={rec['baseline']} asserts={len(rec['assertions'])} "
            f"essential={essential}",
            flush=True,
        )
        return rec

    with ThreadPoolExecutor(max_workers=workers) as pool:
        return list(pool.map(one, sources))


def squash(text: str) -> str:
    """The text without whitespace, for matching assertions across re-extractions."""
    return re.sub(r"\s+", "", text)


def carry_over_keys(rows: list[dict], previous: list[dict]) -> None:
    """Assign keys: the key of the same assertion in ``previous``, else a fresh number.

    An assertion is the same when its problem and line, or problem and
    text, match; fresh numbers continue above every key ever used in the
    corpus, so retired keys are never reused.
    """
    by_loc = {(a["problem"], a["line"]): a["key"] for a in previous}
    by_text = {(a["problem"], squash(a["text"])): a["key"] for a in previous}
    next_idx = {}
    for corpus, prefix in KEY_PREFIX.items():
        used_numbers = [
            int(a["key"].split("-")[1]) for a in previous if a["key"].split("-")[0] == prefix
        ]
        next_idx[corpus] = 1 + max(used_numbers, default=-1)
    used: set[str] = set()
    for row in rows:
        key = by_loc.get((row["problem"], row["line"])) or by_text.get(
            (row["problem"], squash(row["text"]))
        )
        if key is None or key in used:
            key = f"{KEY_PREFIX[row['corpus']]}-{next_idx[row['corpus']]}"
            next_idx[row["corpus"]] += 1
        used.add(key)
        row["key"] = key
        row["new_key"] = key not in {a["key"] for a in previous}


def build_dataset(records: list[dict], previous: list[dict], settings: VerusSettings) -> dict:
    """The dataset of every essential assertion, with per-program and count blocks."""
    rows = [
        {"corpus": rec["corpus"], "problem": rec["problem"], "source_path": rec["source_path"], **a}
        for rec in records
        for a in rec["assertions"]
        if a["essential"]
    ]
    carry_over_keys(rows, previous)
    rows.sort(key=lambda r: (r["corpus"], r["problem"], r["line"]))
    ordered = [{k: r.get(k) for k in ROW_FIELDS} for r in rows]
    passing = [r for r in records if r["baseline"] == "pass"]
    statuses = ("pass", "fail", "timeout", "invalid", "wall-timeout")
    counts = {
        "programs": len(records),
        "baseline": {s: sum(r["baseline"] == s for r in records) for s in statuses},
        "asserts_probed": sum(len(r["assertions"]) for r in passing),
        "removal_fails": sum(a["removal"] in FAILING for r in passing for a in r["assertions"]),
        "removal_invalid": sum(a["removal"] == "invalid" for r in passing for a in r["assertions"]),
        "unstable": sum(
            a["removal"] in FAILING and not a["essential"] for r in passing for a in r["assertions"]
        ),
        "essential": len(ordered),
        "removal": {s: sum(r["removal"] == s for r in ordered) for s in FAILING},
        "new": sum(1 for r in ordered if r["new_key"]),
        **{c: sum(r["corpus"] == c for r in ordered) for c in ("CF-V", "VB")},
    }
    return {
        "description": (
            "Essential Verus assertions: every ghost assert of a file whose "
            "baseline verifies fully is removed by character range; it is essential when the "
            "enclosing function then fails (removal: fail, timeout = rlimit exceeded and "
            "re-checked at twice the rlimit in removal_confirm, wall-timeout = safety net) and "
            "still fails with the inert 'let ghost placebo_term = 0int;' in its place (placebo). "
            "A removal that no longer compiles (invalid) is not essential. removal_errors are the "
            "failing obligations on removal, in source line numbers."
        ),
        "toolchain": settings.describe(),
        "counts": counts,
        "programs": [
            {
                k: rec[k]
                for k in ("corpus", "problem", "source_path", "baseline", "baseline_confirm")
            }
            | {"asserts": len(rec["assertions"])}
            for rec in records
        ],
        "assertions": ordered,
    }


def main() -> int:
    """Command line entry point."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--solver", choices=config.SOLVERS, default="z3")
    parser.add_argument("--programs", nargs="*", help="only these problems (default: every file)")
    parser.add_argument("--workers", type=int, default=6)
    parser.add_argument("--out", type=Path, help="output dataset (default: the recorded one)")
    parser.add_argument(
        "--cache-dir", type=Path, help="per-file cache (default work/verus_extract_<solver>)"
    )
    parser.add_argument(
        "--previous",
        type=Path,
        help="dataset whose keys are carried over (default: the recorded one; skipped when absent)",
    )
    args = parser.parse_args()
    recorded = CONFIGURATIONS[f"verus_{args.solver}"]["dataset"]
    out_path = args.out or recorded
    previous_path = args.previous or recorded
    cache_dir = args.cache_dir or config.WORK / f"verus_extract_{args.solver}"
    settings = VerusSettings(args.solver)

    sources = select_programs(verus_sources(), args.programs)
    print(f"{len(sources)} files")
    with tempfile.TemporaryDirectory(prefix="verus_extract_") as tmpdir:
        records = probe_programs(sources, Path(tmpdir), settings, args.workers, cache_dir)
    previous = json.loads(previous_path.read_text())["assertions"] if previous_path.exists() else []
    dataset = build_dataset(records, previous, settings)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(json.dumps(dataset, indent=1) + "\n")
    print(json.dumps(dataset["counts"], indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

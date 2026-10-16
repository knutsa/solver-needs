"""Calibrate the Dafny resource limits against the baseline programs.

Z3: every corpus program is verified once under a 30 s time limit with
Dafny's text log enabled; the largest per-batch resource count
(``Maximum assertion batch resource count``) of every passing program
gives the limit under which every baseline verifies with margin. The
value is in raw Z3 rlimit units, which Dafny passes to Z3 unchanged.

cvc5: Dafny's log carries no cvc5 resource count, so a ladder of
``--rlimit-per`` values is tried in turn and the smallest one under which
each program verifies is recorded.

Usage::

    uv run python -m solver_needs.dafny.calibrate [--solver z3|cvc5] [--workers 12]
        [--time-limit 30]

Writes ``work/calibration_<solver>.json``.
"""

import argparse
import json
import re
import subprocess
import tempfile
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from solver_needs import config
from solver_needs.corpora import dafny_sources
from solver_needs.dafny.verify import DafnySettings, parse_summary, verify

BATCH_RE = re.compile(r"Maximum assertion batch resource count: (\d+)")
OVERALL_RE = re.compile(r"Overall resource count: (\d+)")
CVC5_LADDER = (10_000_000, 30_000_000, 100_000_000, 300_000_000, 1_000_000_000)


def measure_z3(corpus: str, problem: str, path: Path, tmp: Path, time_limit: int) -> dict:
    """Verify one program under a time limit and read Z3's resource counts from the log."""
    log = tmp / f"{corpus}_{problem[:60]}.log"
    cmd = [
        "dotnet",
        str(config.dafny_dll()),
        "verify",
        str(path),
        "--allow-warnings",
        "--cores",
        "1",
        "--solver-path",
        str(config.z3()),
        "--verification-time-limit",
        str(time_limit),
        "--log-format",
        f"text;LogFileName={log}",
    ]
    t0 = time.time()
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=config.DAFNY_WALL_TIMEOUT)
    wall = time.time() - t0
    text = log.read_text() if log.exists() else ""
    batches = [int(x) for x in BATCH_RE.findall(text)]
    overall = [int(x) for x in OVERALL_RE.findall(text)]
    rec = {
        "corpus": corpus,
        "problem": problem,
        "status": parse_summary(proc.stdout + proc.stderr)[0],
        "wall_seconds": round(wall, 1),
        "max_batch_resource": max(batches) if batches else None,
        "max_symbol_resource": max(overall) if overall else None,
        "symbols": len(overall),
    }
    print(
        f"{corpus} {problem[:50]:50s} {rec['status']:8s} {wall:6.1f}s "
        f"max_batch={rec['max_batch_resource']}",
        flush=True,
    )
    return rec


def measure_cvc5(corpus: str, problem: str, path: Path, time_limit: int) -> dict:
    """Try the ladder in turn; record the smallest limit under which the file verifies."""
    t0 = time.time()
    status, limit = None, CVC5_LADDER[-1]
    for limit in CVC5_LADDER:
        settings = DafnySettings("cvc5", limit, time_limit)
        status, _ = verify(path, settings)
        if status == "pass":
            break
    rec = {
        "corpus": corpus,
        "problem": problem,
        "status": status,
        "wall_seconds": round(time.time() - t0, 1),
        "min_passing_limit": limit if status == "pass" else None,
    }
    print(
        f"{corpus} {problem[:50]:50s} {status!s:8s} {rec['wall_seconds']:6.1f}s "
        f"min_passing_limit={rec['min_passing_limit']}",
        flush=True,
    )
    return rec


def summarize_z3(records: list[dict], time_limit: int) -> dict:
    """The resource count every passing baseline stays under, and the heaviest programs."""
    passing = [r for r in records if r["status"] == "pass" and r["max_batch_resource"] is not None]
    ranked = sorted(passing, key=lambda r: r["max_batch_resource"], reverse=True)
    return {
        "solver": "z3",
        "time_limit_used": time_limit,
        "programs": len(records),
        "baseline_pass": len(passing),
        "max_batch_resource_over_passing": max(
            (r["max_batch_resource"] for r in passing), default=None
        ),
        "heaviest_passing": [
            {k: r[k] for k in ("problem", "max_batch_resource", "wall_seconds")}
            for r in ranked[:10]
        ],
        "records": records,
    }


def summarize_cvc5(records: list[dict], time_limit: int) -> dict:
    """How many baselines pass under each ladder step, and the largest limit needed."""
    passing = [r["min_passing_limit"] for r in records if r["status"] == "pass"]
    return {
        "solver": "cvc5",
        "time_limit_used": time_limit,
        "limits_tried": list(CVC5_LADDER),
        "programs": len(records),
        "baseline_pass": len(passing),
        "passing_by_min_limit": {str(limit): passing.count(limit) for limit in CVC5_LADDER},
        "max_min_passing_limit": max(passing) if passing else None,
        "records": records,
    }


def main() -> int:
    """Command line entry point."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--solver", choices=config.SOLVERS, default="z3")
    parser.add_argument("--workers", type=int, default=12)
    parser.add_argument("--time-limit", type=int, default=30)
    args = parser.parse_args()
    sources = dafny_sources()
    with (
        tempfile.TemporaryDirectory(prefix="calibrate_") as tmpdir,
        ThreadPoolExecutor(max_workers=args.workers) as pool,
    ):
        if args.solver == "cvc5":
            records = list(
                pool.map(lambda s: measure_cvc5(s[0], s[1], s[2], args.time_limit), sources)
            )
            summary = summarize_cvc5(records, args.time_limit)
        else:
            records = list(
                pool.map(
                    lambda s: measure_z3(s[0], s[1], s[2], Path(tmpdir), args.time_limit), sources
                )
            )
            summary = summarize_z3(records, args.time_limit)
    config.WORK.mkdir(exist_ok=True)
    out = config.WORK / f"calibration_{args.solver}.json"
    out.write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps({k: v for k, v in summary.items() if k != "records"}, indent=1))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

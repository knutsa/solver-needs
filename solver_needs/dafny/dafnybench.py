"""Place the DB corpus from a DafnyBench checkout.

Every ``ground_truth/*.dfy`` program of DafnyBench is copied verbatim to
``data/corpora/DB/DB_<name>.dfy`` (the name with characters outside
``[A-Za-z0-9_.-]`` replaced by ``_``), and ``MANIFEST.json`` next to them
records the DafnyBench commit and the original file names. The extractor
then probes every one of those programs; programs without an assert only
get a baseline run.

The checkout must be at ``DAFNYBENCH_COMMIT``::

    git clone https://github.com/sun-wendy/DafnyBench.git
    git -C DafnyBench checkout 0cd28feed9cd0179b07fdb9d002f8c39063658e4
    uv run python -m solver_needs.dafny.dafnybench --dafnybench DafnyBench
"""

import argparse
import json
import re
import subprocess
from pathlib import Path

from solver_needs import config

DAFNYBENCH_REPO = "https://github.com/sun-wendy/DafnyBench"
DAFNYBENCH_COMMIT = "0cd28feed9cd0179b07fdb9d002f8c39063658e4"
GROUND_TRUTH = Path("DafnyBench") / "dataset" / "ground_truth"


def sanitize(stem: str) -> str:
    """The corpus file name of a DafnyBench program: ``DB_`` plus the sanitized stem."""
    return "DB_" + re.sub(r"[^A-Za-z0-9_.-]", "_", stem)[:120]


def checkout_commit(repo: Path) -> str:
    """The commit a git checkout is at."""
    result = subprocess.run(
        ["git", "-C", str(repo), "rev-parse", "HEAD"], capture_output=True, text=True, check=True
    )
    return result.stdout.strip()


def copy_ground_truth(ground_truth: Path, out_dir: Path) -> dict[str, str]:
    """Copy every program; returns ``{program name: original file name}``.

    Fails if two DafnyBench files sanitize to the same name, or if a file
    already in ``out_dir`` differs from its DafnyBench original (the corpus
    is a verbatim copy, never an edited one).
    """
    files = sorted(ground_truth.glob("*.dfy"))
    if not files:
        raise SystemExit(f"no .dfy files under {ground_truth}")
    out_dir.mkdir(parents=True, exist_ok=True)
    names: dict[str, str] = {}
    for src in files:
        name = sanitize(src.stem)
        if name in names:
            raise SystemExit(f"{src.name} and {names[name]} both sanitize to {name}")
        names[name] = src.name
        dst = out_dir / f"{name}.dfy"
        content = src.read_bytes()
        if dst.exists() and dst.read_bytes() != content:
            raise SystemExit(
                f"{dst} differs from DafnyBench {src.name}; the corpus must be a verbatim copy"
            )
        dst.write_bytes(content)
    return names


def main() -> int:
    """Command line entry point."""
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--dafnybench", type=Path, required=True, help="DafnyBench checkout")
    parser.add_argument("--out", type=Path, default=config.CORPORA / "DB")
    args = parser.parse_args()

    commit = checkout_commit(args.dafnybench)
    if commit != DAFNYBENCH_COMMIT:
        raise SystemExit(
            f"DafnyBench checkout is at {commit}, expected {DAFNYBENCH_COMMIT}; "
            f"run: git -C {args.dafnybench} checkout {DAFNYBENCH_COMMIT}"
        )
    names = copy_ground_truth(args.dafnybench / GROUND_TRUTH, args.out)
    manifest = {
        "dafnybench_repo": DAFNYBENCH_REPO,
        "dafnybench_commit": commit,
        "programs": len(names),
        "original_names": names,
    }
    (args.out / "MANIFEST.json").write_text(json.dumps(manifest, indent=1, sort_keys=True) + "\n")
    print(f"{len(names)} DafnyBench programs in {args.out} (commit {commit[:12]})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

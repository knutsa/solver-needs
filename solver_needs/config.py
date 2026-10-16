"""Repository layout, toolchain locations and the resource limits of the paper.

Toolchain binaries are looked up in ``tools/`` (populated by
``tools/setup_toolchain.sh``) unless an environment variable names another
location:

* ``SOLVER_NEEDS_DAFNY_DLL``: ``Dafny.dll`` of the Dafny fork, or of the stock
  Dafny release when the AST mapping step is not needed.
* ``SOLVER_NEEDS_Z3``: the Z3 binary used for Dafny (the paper uses 4.12.1).
* ``SOLVER_NEEDS_VERUS``: the ``verus`` binary (the paper uses 0.2026.02.22,
  with the Z3 it bundles).
* ``SOLVER_NEEDS_CVC5``: the cvc5 binary (the paper uses 1.1.2).
"""

import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "data"
CORPORA = DATA / "corpora"
ESSENTIAL = DATA / "essential"
BENCHMARK_SETS = DATA / "benchmark_sets"
RESULTS = ROOT / "results"
TOOLS = ROOT / "tools"
WORK = ROOT / "work"

SOLVERS = ("z3", "cvc5")


def _tool(env: str, *candidates: Path) -> Path:
    """The path named by ``env``, else the first existing candidate, else the first candidate."""
    override = os.environ.get(env)
    if override:
        return Path(override).expanduser()
    for candidate in candidates:
        if candidate.exists():
            return candidate
    return candidates[0]


def dafny_dll() -> Path:
    """``Dafny.dll`` of the fork if built, else of the downloaded release."""
    return _tool(
        "SOLVER_NEEDS_DAFNY_DLL",
        TOOLS / "dafny-fork" / "Binaries" / "Dafny.dll",
        TOOLS / "dafny" / "dafny" / "Dafny.dll",
    )


def dafny_prelude() -> Path:
    """The Boogie prelude shipped next to the Dafny in use; the AX probe extends it."""
    return dafny_dll().with_name("DafnyPrelude.bpl")


def z3() -> Path:
    """The Z3 binary passed to Dafny."""
    return _tool("SOLVER_NEEDS_Z3", TOOLS / "z3" / "bin" / "z3")


def verus() -> Path:
    """The Verus binary; its bundled Z3 sits next to it."""
    return _tool("SOLVER_NEEDS_VERUS", TOOLS / "verus" / "verus")


def cvc5() -> Path:
    """The cvc5 binary, shared by the Dafny launcher and Verus's solver switch."""
    return _tool("SOLVER_NEEDS_CVC5", TOOLS / "cvc5" / "bin" / "cvc5")


CVC5_LAUNCHER = TOOLS / "cvc5_dafny.sh"

# Dafny resource limits. Z3 runs under a resource limit of 1e9
# raw rlimit units, passed unchanged as (set-option :rlimit N), plus a
# wall-clock cap per verify call of ten times the ~30 s the limit was tuned
# to. cvc5 runs under 1e8 cvc5 resource units per check (set by the
# calibration in solver_needs.dafny.calibrate) and a 60 s Dafny time limit.
DAFNY_RESOURCE_LIMIT = {"z3": 1_000_000_000, "cvc5": 100_000_000}
DAFNY_TIME_LIMIT = {"z3": 300, "cvc5": 60}
DAFNY_WALL_TIMEOUT = 1800  # safety net only; a hit is reported as wall-timeout, never a verdict
DAFNY_SECOND_SEED = 1  # Boogie /randomSeed of the extractor's second removal run

# Verus runs under its default --rlimit 10; removals that exhaust it are
# confirmed once at --rlimit 20. The wall-clock caps are safety nets.
VERUS_RLIMIT = 10.0
VERUS_CONFIRM_RLIMIT = 2 * VERUS_RLIMIT
VERUS_EXTRACT_WALL_TIMEOUT = 300
VERUS_PROBE_WALL_TIMEOUT = 120
VERUS_FUEL = 20  # reveal_with_fuel(f, 20) in the FUEL probe

MAX_SEEDS = 8  # terms tried by the INST probe
MAX_EQUALITY_SEEDS = 3  # equalities tried by the equality-seed probe

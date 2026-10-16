"""Running Verus under the paper's resource limit and reading its verdict.

Verus runs with ``--crate-type=lib`` under its default ``--rlimit 10``,
with Z3 (its bundled one) or cvc5 (``-V cvc5``, located through
``VERUS_CVC5_PATH``).
"""

import os
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path

from solver_needs import config

ERROR_RE = re.compile(r"^error(?:\[E\d+\])?: (.*)\n\s*--> \S+?:(\d+):\d+", re.M)
SUMMARY_RE = re.compile(r"verification results:: (\d+) verified, (\d+) errors")
BUDGET_MESSAGE = "Resource limit (rlimit) exceeded"


@dataclass(frozen=True)
class VerusSettings:
    """The solver of a Verus run; the rlimit is the paper's for every run."""

    solver: str

    def flags(self) -> tuple[str, ...]:
        """Extra Verus flags selecting the solver."""
        return ("-V", "cvc5") if self.solver == "cvc5" else ()

    def env(self) -> dict[str, str]:
        """Environment of a Verus run (cvc5's location when it is the solver)."""
        env = dict(os.environ)
        if self.solver == "cvc5":
            env["VERUS_CVC5_PATH"] = str(config.cvc5())
        return env

    def describe(self) -> dict:
        """The toolchain block recorded in datasets and result files."""
        return {
            "verus": verus_version(),
            "solver": self.solver,
            "solver_version": solver_version(self.solver),
            "verify_flags": [
                "--crate-type=lib",
                "--rlimit",
                str(config.VERUS_RLIMIT),
                "--no-auto-recommends-check",
            ],
            "rlimit": config.VERUS_RLIMIT,
            "confirm_rlimit": config.VERUS_CONFIRM_RLIMIT,
        }


def verus_version() -> str:
    """The version string of the Verus in use."""
    out = subprocess.run(
        [str(config.verus()), "--version"], capture_output=True, text=True, check=True
    )
    return out.stdout.split("Version:")[1].split()[0]


def solver_version(solver: str) -> str:
    """Version string of the SMT backend (Verus's bundled Z3, or cvc5)."""
    if solver == "cvc5":
        out = subprocess.run(
            [str(config.cvc5()), "--version"], capture_output=True, text=True, check=True
        )
        return "cvc5 " + out.stdout.split("version")[1].split()[0]
    z3 = config.verus().parent / "z3"
    out = subprocess.run([str(z3), "--version"], capture_output=True, text=True, check=True)
    return out.stdout.strip()


def run(
    path: Path,
    settings: VerusSettings,
    rlimit: float = config.VERUS_RLIMIT,
    extra: tuple[str, ...] = (),
    wall_timeout: int = config.VERUS_PROBE_WALL_TIMEOUT,
) -> str | None:
    """Run Verus on ``path``; returns its combined output, or None if the wall-clock cap fired."""
    cmd = [
        str(config.verus()),
        str(path),
        "--crate-type=lib",
        "--rlimit",
        str(rlimit),
        "--no-auto-recommends-check",
        *settings.flags(),
        *extra,
    ]
    try:
        proc = subprocess.run(
            cmd, capture_output=True, text=True, timeout=wall_timeout, env=settings.env()
        )
    except subprocess.TimeoutExpired:
        return None
    return proc.stdout + proc.stderr


def probe_status(output: str | None) -> tuple[str, str]:
    """A probe's verdict on the whole file: pass | fail | timeout | invalid."""
    if output is None:
        return "timeout", "TIMEOUT"
    out = output.strip()
    if len(out) > 6000:
        out = out[:3000] + "\n...\n" + out[-2000:]
    if "verification results" not in out:
        return "invalid", out
    if "0 errors" in out:
        return "pass", out
    if "rlimit" in out.lower() or "timed out" in out.lower():
        return "timeout", out
    return "fail", out


def file_status(output: str | None) -> str:
    """An extraction run's verdict on the whole file: pass | fail | invalid | wall-timeout.

    ``fail`` covers rlimit exhaustion too; ``status_within`` separates the
    two per function from the error messages.
    """
    if output is None:
        return "wall-timeout"
    m = SUMMARY_RE.search(output)
    if m is None:
        return "invalid"
    return "pass" if m.group(2) == "0" else "fail"


def error_lines(output: str) -> list[tuple[int, str]]:
    """``(line, message)`` of every error Verus reports with a location; notes are skipped."""
    return [(int(m.group(2)), m.group(1).strip()) for m in ERROR_RE.finditer(output)]


def status_within(status: str, output: str, span: tuple[int, int]) -> tuple[str, int]:
    """Status restricted to the function at ``span`` (1-based lines), plus errors elsewhere.

    ``invalid`` and ``wall-timeout`` pass through: neither is a verdict on
    the function and neither may be read as a pass.
    """
    if status in ("invalid", "wall-timeout"):
        return status, 0
    inside, outside = [], 0
    for line, message in error_lines(output):
        if span[0] <= line <= span[1]:
            inside.append(message)
        else:
            outside += 1
    if not inside:
        return "pass", outside
    if all(BUDGET_MESSAGE in message for message in inside):
        return "timeout", outside
    return "fail", outside


def baseline_status(status: str, output: str) -> str:
    """Whole-file baseline status: pass | fail | timeout | invalid | wall-timeout."""
    if status in ("pass", "invalid", "wall-timeout"):
        return status
    errors = error_lines(output)
    if all(BUDGET_MESSAGE in message for _, message in errors):
        return "timeout"
    return "fail"

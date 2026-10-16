"""Running Dafny under the paper's resource limits and reading its verdict.

A run's status is one of ``pass`` (no error), ``fail`` (a verification
error), ``timeout`` (the solver exhausted its resource or time budget),
``invalid`` (the program does not parse or resolve, or the solver crashed)
and ``wall-timeout`` (the driver's safety net fired; never a verdict).
"""

import os
import re
import signal
import subprocess
from dataclasses import dataclass
from pathlib import Path

from solver_needs import config

SUMMARY_RE = re.compile(
    r"verifier finished with (\d+) (?:assertions )?verified, (\d+) errors?"
    r"(?:, (?P<inconclusive>\d+) inconclusives?)?"
    r"(?:, (?P<timeouts>\d+) time outs?)?"
    r"(?:, (?P<oom>\d+) out of memory)?"
    r"(?:, (?P<oor>\d+) out of resource)?"
    r"(?:, (?P<exc>\d+) solver exceptions)?"
)
ERROR_LINE_RE = re.compile(r"\((\d+),(\d+)\): Error: (.*)")
RELATED_RE = re.compile(r"\((\d+),(\d+)\): Related location")
BUDGET_MESSAGES = ("timed out", "out of resource", "inconclusive")  # inconclusive: cvc5 resourceout


@dataclass(frozen=True)
class DafnySettings:
    """The verifier/solver configuration of a run.

    Attributes:
        solver: ``z3`` or ``cvc5``.
        resource_limit: Z3 rlimit units, or cvc5 resource units per check.
        time_limit: Dafny ``--verification-time-limit`` per verify call in seconds.
    """

    solver: str
    resource_limit: int
    time_limit: int

    @classmethod
    def for_solver(cls, solver: str) -> "DafnySettings":
        """The paper's limits for ``solver``."""
        return cls(solver, config.DAFNY_RESOURCE_LIMIT[solver], config.DAFNY_TIME_LIMIT[solver])

    def describe(self) -> dict:
        """The toolchain block recorded in datasets and result files."""
        return {
            "dafny": dafny_version(),
            "solver": self.solver,
            "solver_version": solver_version(self.solver),
            "resource_limit": self.resource_limit,
            "confirm_resource_limit": 2 * self.resource_limit,
            "time_limit": self.time_limit,
            "second_seed": config.DAFNY_SECOND_SEED,
            "filter_declaration": True,
        }


def dafny_version() -> str:
    """Version string of the Dafny in use."""
    out = subprocess.run(
        ["dotnet", str(config.dafny_dll()), "--version"], capture_output=True, text=True, check=True
    )
    return out.stdout.strip()


def solver_version(solver: str) -> str:
    """Version string of the SMT backend in use."""
    binary = config.cvc5() if solver == "cvc5" else config.z3()
    out = subprocess.run([str(binary), "--version"], capture_output=True, text=True, check=True)
    return out.stdout.strip().splitlines()[0]


def parse_summary(out: str) -> tuple[str, str]:
    """Status from Dafny's output: pass | fail | timeout | invalid.

    ``timeout`` means the budget was exhausted (out of resource, or the time
    limit). Dafny prints "0 errors, 1 out of resource", so the error count
    alone never decides.
    """
    out = out.strip()
    if "resolution/type errors" in out or "parse errors" in out:
        return "invalid", out[-20000:]
    if "BadExprFromProver" in out:
        # cvc5 only: the solver answered sat and Boogie crashed converting the
        # counterexample model (its parser knows Bool, Int, BitVec and Array,
        # and the Dafny prelude puts reals in every model). The summary then
        # says 0 errors although the obligation failed: a definite failure,
        # reported at the declaration's line rather than the obligation's.
        return "fail", out[-20000:]
    summary = SUMMARY_RE.search(out)
    if not summary:
        return "invalid", out[-20000:]
    if summary.group("oom") or summary.group("exc"):
        return "invalid", out[-20000:]
    if summary.group("timeouts") or summary.group("oor") or summary.group("inconclusive"):
        # inconclusive: the solver gave up without a verdict (cvc5's resourceout
        # arrives this way); a budget outcome, never a definite failure
        return "timeout", out[-20000:]
    if summary.group(2) != "0":
        return "fail", out[-20000:]
    return "pass", out[-20000:]


def _command(
    dfy: Path,
    settings: DafnySettings,
    resource_limit: int,
    prelude: Path | None,
    seed: int | None,
    filter_lines: tuple[int, int] | None,
) -> tuple[list[str], dict[str, str]]:
    cmd = [
        "dotnet",
        str(config.dafny_dll()),
        "verify",
        str(dfy),
        "--allow-warnings",
        "--cores",
        "1",
        "--resource-limit",
        str(resource_limit),
        "--verification-time-limit",
        str(settings.time_limit),
    ]
    env = dict(os.environ)
    if settings.solver == "cvc5":
        # Boogie sends the resource limit, seed and time limit to Z3 only, so
        # the launcher script puts them on cvc5's command line.
        cmd += ["--solver-path", str(config.CVC5_LAUNCHER), "--boogie", "/proverOpt:SOLVER=cvc5"]
        env["CVC5_PATH"] = str(config.cvc5())
        env["CVC5_RLIMIT_PER"] = str(resource_limit)
        if settings.time_limit:
            env["CVC5_TLIMIT_PER"] = str(
                settings.time_limit * 1000
            )  # Boogie's limit does not stop cvc5
        if seed is not None:
            env["CVC5_SEED"] = str(seed)
    else:
        cmd += ["--solver-path", str(config.z3())]
    if prelude is not None:
        cmd += ["--prelude", str(prelude)]
    if seed is not None:
        cmd += ["--boogie", f"/randomSeed:{seed}"]
    if filter_lines is not None:
        cmd += [f"--filter-position=:{filter_lines[0]}-{filter_lines[1]}"]
    return cmd, env


def verify(
    dfy: Path,
    settings: DafnySettings,
    prelude: Path | None = None,
    resource_limit: int | None = None,
    seed: int | None = None,
    filter_lines: tuple[int, int] | None = None,
) -> tuple[str, str]:
    """Verify ``dfy``; returns ``(status, output)``.

    Args:
        dfy: the program to verify.
        settings: solver and limits.
        resource_limit: overrides the settings' resource limit for this run.
        prelude: a Boogie prelude replacing Dafny's own (the AX probe).
        seed: Boogie's ``/randomSeed`` (VC randomization plus the solver's random seeds).
        filter_lines: verify only the declarations within this line range.
    """
    limit = settings.resource_limit if resource_limit is None else resource_limit
    cmd, env = _command(dfy, settings, limit, prelude, seed, filter_lines)
    # Dafny runs in its own process group and the whole group is killed
    # afterwards: a solver that has already answered "out of resource"
    # otherwise keeps computing as an orphan.
    proc = subprocess.Popen(
        cmd,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
        env=env,
    )
    try:
        stdout, stderr = proc.communicate(timeout=config.DAFNY_WALL_TIMEOUT)
    except subprocess.TimeoutExpired:
        stdout = stderr = ""
        hit_wall = True
    else:
        hit_wall = False
    finally:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            pass  # group already gone; macOS reports EPERM once the leader has exited
        proc.wait()
    if hit_wall:
        # the wall-clock safety net, not a solver verdict: kept distinct from
        # "timeout" (budget exhausted) so it can never count as pass or essential
        return "wall-timeout", "WALL-TIMEOUT"
    return parse_summary(stdout + stderr)


def all_errors(output: str) -> list[dict]:
    """Every verification error with the related locations printed after it.

    ``related_line`` is the first related location (the obligation, e.g. the
    ensures clause, when the error is reported at a return or call site);
    ``related_lines`` lists all of them.
    """
    errors = []
    matches = list(ERROR_LINE_RE.finditer(output))
    for i, err in enumerate(matches):
        chunk_end = matches[i + 1].start() if i + 1 < len(matches) else len(output)
        related = [int(m.group(1)) for m in RELATED_RE.finditer(output, err.end(), chunk_end)]
        errors.append(
            {
                "line": int(err.group(1)),
                "message": err.group(3).strip(),
                "related_line": related[0] if related else None,
                "related_lines": related,
            }
        )
    return errors


def errors_to_source_lines(
    errors: list[dict], removed_newlines: int, start_line: int
) -> list[dict]:
    """Map line numbers reported on a removed variant back to the source.

    Lines after the removed statement's first line (1-based ``start_line``)
    shift by the number of newlines the statement spanned.
    """

    def back(ln: int | None) -> int | None:
        return ln + removed_newlines if ln and ln > start_line else ln

    mapped = []
    for error in errors:
        m = dict(error)
        for field in ("line", "related_line"):
            m[field] = back(error.get(field))
        if "related_lines" in error:
            m["related_lines"] = [back(ln) for ln in error["related_lines"]]
        mapped.append(m)
    return mapped


def status_within(status: str, output: str, span: tuple[int, int]) -> tuple[str, int]:
    """Status restricted to the declaration at ``span`` (1-based lines), plus errors elsewhere.

    ``invalid`` and ``wall-timeout`` pass through unchanged: neither is a
    verdict and neither may be read as a pass. Removing an assert can only
    change the verification of its own declaration, so errors reported in
    other declarations are counted but ignored.
    """
    if status in ("invalid", "wall-timeout"):
        return status, 0
    inside, outside = [], 0
    for m in ERROR_LINE_RE.finditer(output):
        if span[0] <= int(m.group(1)) <= span[1]:
            inside.append(m.group(3))
        else:
            outside += 1
    if not inside:
        return "pass", outside
    if all(any(budget in msg for budget in BUDGET_MESSAGES) for msg in inside):
        return "timeout", outside
    return "fail", outside

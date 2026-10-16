"""The four program corpora and where the extractors find them.

``data/corpora/<corpus>/`` holds exactly the files the extractors read:

* ``CF-D``: Codeforces-derived Dafny programs annotated by an LLM agent, one
  ``<problem>.dfy`` per problem.
* ``DB``: the ground-truth programs of DafnyBench, one ``DB_<name>.dfy`` per
  program (``MANIFEST.json`` records the original names and commit).
* ``CF-V``: the CF-D problems translated to Verus, one ``<problem>.rs``.
* ``VB``: the verified solutions of the four VerusBench suites,
  ``<suite>/<name>.rs``.
"""

from pathlib import Path

from solver_needs.config import CORPORA, ROOT

DAFNY_CORPORA = ("CF-D", "DB")
VERUS_CORPORA = ("CF-V", "VB")
VB_SUITES = ("CloverBench", "Diffy", "MBPP", "Misc")

KEY_PREFIX = {"CF-D": "CF", "DB": "DB", "CF-V": "V", "VB": "VB"}
"""Prefix of the assertion keys of each corpus (``CF-12``, ``DB-3``, ``V-7``, ``VB-1``)."""


def corpus_of_key(key: str) -> str:
    """The corpus an assertion key belongs to, from its prefix."""
    prefix = key.split("-")[0]
    for corpus, p in KEY_PREFIX.items():
        if p == prefix:
            return corpus
    raise ValueError(f"unknown key prefix: {key}")


def dafny_sources() -> list[tuple[str, str, Path]]:
    """``(corpus, problem, path)`` of every Dafny program, CF-D first, in name order."""
    out = [("CF-D", p.stem, p) for p in sorted((CORPORA / "CF-D").glob("*.dfy"))]
    out += [("DB", p.stem, p) for p in sorted((CORPORA / "DB").glob("*.dfy"))]
    return out


def verus_sources() -> list[tuple[str, str, Path]]:
    """``(corpus, problem, path)`` of every Verus program, CF-V first, then VB by suite."""
    out = [("CF-V", p.stem, p) for p in sorted((CORPORA / "CF-V").glob("*.rs"))]
    for suite in VB_SUITES:
        out += [
            ("VB", f"{suite}/{p.stem}", p) for p in sorted((CORPORA / "VB" / suite).glob("*.rs"))
        ]
    return out


def select_programs(
    sources: list[tuple[str, str, Path]], programs: list[str] | None
) -> list[tuple[str, str, Path]]:
    """Restrict ``sources`` to the named problems (``--programs``); all of them when None."""
    if not programs:
        return sources
    wanted = set(programs)
    chosen = [s for s in sources if s[1] in wanted]
    missing = wanted - {s[1] for s in chosen}
    if missing:
        raise SystemExit(f"unknown programs: {sorted(missing)}")
    return chosen


def relative(path: Path) -> str:
    """A corpus path as recorded in the datasets: relative to the repository root."""
    return str(path.resolve().relative_to(ROOT))

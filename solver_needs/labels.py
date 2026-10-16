"""Mechanism labels, the four verifier/solver configurations and the benchmark task sets.

A label is one of ``AX``, ``INST-forall``, ``INST-witness``, ``NLA``, ``FUEL``
and ``Other``; the family of a label folds the two INST forms into ``INST``.
"""

import json
from pathlib import Path
from typing import TypedDict

from solver_needs.config import BENCHMARK_SETS, ESSENTIAL, RESULTS
from solver_needs.corpora import DAFNY_CORPORA, VERUS_CORPORA

FAMILIES = ("AX", "INST", "NLA", "FUEL", "Other")


def family(label: str) -> str:
    """The family of a label (``INST-forall`` and ``INST-witness`` are ``INST``)."""
    return label.split("-")[0]


class Configuration(TypedDict):
    """One verifier/solver pair: its dataset, recorded results and applicable probes."""

    verifier: str
    solver: str
    corpora: tuple[str, ...]
    dataset: Path
    results: Path
    families: tuple[str, ...]  # probe families in the order the classifier tries them
    benchmark_set: Path | None


CONFIGURATIONS: dict[str, Configuration] = {
    "dafny_z3": {
        "verifier": "Dafny",
        "solver": "Z3",
        "corpora": DAFNY_CORPORA,
        "dataset": ESSENTIAL / "essential_dafny_z3.json",
        "results": RESULTS / "dafny_z3",
        "families": ("INST", "AX"),
        "benchmark_set": BENCHMARK_SETS / "dafny_tasks.json",
    },
    "dafny_cvc5": {
        "verifier": "Dafny",
        "solver": "cvc5",
        "corpora": DAFNY_CORPORA,
        "dataset": ESSENTIAL / "essential_dafny_cvc5.json",
        "results": RESULTS / "dafny_cvc5",
        "families": ("INST", "AX"),
        "benchmark_set": None,
    },
    "verus_z3": {
        "verifier": "Verus",
        "solver": "Z3",
        "corpora": VERUS_CORPORA,
        "dataset": ESSENTIAL / "essential_verus_z3.json",
        "results": RESULTS / "verus_z3",
        "families": ("FUEL", "INST", "AX", "NLA"),
        "benchmark_set": BENCHMARK_SETS / "verus_tasks.json",
    },
    "verus_cvc5": {
        "verifier": "Verus",
        "solver": "cvc5",
        "corpora": VERUS_CORPORA,
        "dataset": ESSENTIAL / "essential_verus_cvc5.json",
        "results": RESULTS / "verus_cvc5",
        "families": ("FUEL", "INST", "AX"),
        "benchmark_set": None,
    },
}


def load_dataset(path: Path) -> dict:
    """An essential-assertion dataset as written by the extractors."""
    return json.loads(path.read_text())


def load_probes(results: Path) -> dict[str, dict]:
    """The recorded probe evidence of a configuration, by assertion key."""
    rows = json.loads((results / "probes.json").read_text())
    return {row["key"]: row for row in rows}


def load_labels(results: Path) -> dict[str, str]:
    """The recorded label of every classified assertion of a configuration."""
    return json.loads((results / "labels.json").read_text())["labels"]


def load_benchmark_set(path: Path) -> dict:
    """A benchmark task set: ``labels`` (key -> family) and ``aliases``."""
    return json.loads(path.read_text())


def benchmark_set(configuration: Configuration) -> Path:
    """The benchmark task set of a configuration; only the Z3 configurations have one."""
    path = configuration["benchmark_set"]
    if path is None:
        raise ValueError(
            f"{configuration['verifier']} + {configuration['solver']} has no benchmark set"
        )
    return path


def benchmark_rows(benchmark: dict, rows: dict[str, dict]) -> dict[str, dict]:
    """The recorded rows of the benchmark tasks present in a run, keyed by task key.

    ``aliases`` maps a task key to the key the same assertion carries in the
    recorded run; tasks absent from the run are left out.
    """
    aliases = benchmark.get("aliases", {})
    return {k: rows[aliases.get(k, k)] for k in benchmark["labels"] if aliases.get(k, k) in rows}

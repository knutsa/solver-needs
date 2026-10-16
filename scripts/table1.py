"""Table 1: essential assertions by mechanism, per verifier/solver configuration and corpus.

Printed from the recorded results of every configuration, once over every
essential assertion of the recorded run and once restricted to the
benchmark task sets (the 320 Dafny and 462 Verus repair tasks), next
to the labels those tasks carry in the paper.

Usage::

    uv run python scripts/table1.py
"""

from collections import Counter

from solver_needs.corpora import corpus_of_key
from solver_needs.labels import (
    CONFIGURATIONS,
    FAMILIES,
    Configuration,
    benchmark_rows,
    family,
    load_benchmark_set,
    load_labels,
)


def row(name: str, labels: list[str], families: tuple[str, ...]) -> str:
    """One table row: total and count (share) per family, ``n/a`` for families not probed."""
    counts = Counter(labels)
    total = len(labels)
    cells = []
    for f in FAMILIES:
        if f not in families and f != "Other":
            cells.append("n/a")
        else:
            cells.append(f"{counts[f]} ({100 * counts[f] / total:.0f}%)" if total else "0")
    return f"| {name} | {total} | " + " | ".join(cells) + " |"


def section(title: str, by_corpus: dict[str, list[str]], configuration: Configuration) -> list[str]:
    """The rows of one configuration: one per corpus and one for all."""
    families = configuration["families"]
    lines = [f"| {title} | | " + " | ".join("" for _ in FAMILIES) + " |"]
    for corpus, labels in by_corpus.items():
        lines.append(row(corpus, labels, families))
    lines.append(row("all", [lab for labs in by_corpus.values() for lab in labs], families))
    return lines


def recorded(name: str, configuration: Configuration) -> list[str]:
    """Rows for every essential assertion of the recorded run."""
    labels = load_labels(configuration["results"])
    by_corpus = {c: [] for c in configuration["corpora"]}
    for key, label in labels.items():
        by_corpus[corpus_of_key(key)].append(family(label))
    return section(
        f"{configuration['verifier']} + {configuration['solver']}, recorded run",
        by_corpus,
        configuration,
    )


def on_benchmark(name: str, configuration: Configuration) -> list[str]:
    """Rows restricted to the benchmark tasks, with the recorded labels and with the paper's."""
    path = configuration["benchmark_set"]
    if path is None:
        return []
    benchmark = load_benchmark_set(path)
    labels = {k: {"label": v} for k, v in load_labels(configuration["results"]).items()}
    present = benchmark_rows(benchmark, labels)
    run_by_corpus = {c: [] for c in configuration["corpora"]}
    paper_by_corpus = {c: [] for c in configuration["corpora"]}
    for key in benchmark["labels"]:
        paper_by_corpus[corpus_of_key(key)].append(benchmark["labels"][key])
        if key in present:
            run_by_corpus[corpus_of_key(key)].append(family(present[key]["label"]))
    verifier = f"{configuration['verifier']} + {configuration['solver']}"
    out = section(
        f"{verifier}, benchmark tasks present in the recorded run, recorded labels",
        run_by_corpus,
        configuration,
    )
    out += section(
        f"{verifier}, benchmark tasks, labels of the paper", paper_by_corpus, configuration
    )
    return out


def main() -> None:
    """Print Table 1 as Markdown."""
    print("| Configuration / corpus | Total | " + " | ".join(FAMILIES) + " |")
    print("|---|---|" + "---|" * len(FAMILIES))
    for name, configuration in CONFIGURATIONS.items():
        for line in recorded(name, configuration) + on_benchmark(name, configuration):
            print(line)


if __name__ == "__main__":
    main()

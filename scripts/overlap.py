"""Probe overlap and label-order sensitivity on the benchmark task sets.

The recorded run lists, for every essential assertion, every probe family
that restores verification (``categories`` in ``probes.json``). Restricted
to the benchmark tasks, this script prints

* coverage: how many tasks the recorded run contains,
* the family overlap matrix and the multiset of passing-family combinations,
* the label distribution under every family order (first passing family wins),
* the confusion between the labels of the paper and those of the recorded run.

Usage::

    uv run python scripts/overlap.py [--configuration dafny_z3|verus_z3]
"""

import argparse
import itertools
from collections import Counter

from solver_needs.labels import (
    CONFIGURATIONS,
    Configuration,
    benchmark_rows,
    benchmark_set,
    family,
    load_benchmark_set,
    load_probes,
)


def matrix(cats: dict[str, set[str]], families: tuple[str, ...]) -> list[str]:
    """Diagonal: tasks the family repairs; off-diagonal: tasks both repair."""
    out = ["| | " + " | ".join(families) + " |", "|---|" + "---|" * len(families)]
    for a in families:
        cells = [str(sum(1 for c in cats.values() if a in c and b in c)) for b in families]
        out.append(f"| {a} | " + " | ".join(cells) + " |")
    return out


def order_table(cats: dict[str, set[str]], families: tuple[str, ...]) -> list[str]:
    """Label distribution under every family order; orders with identical outcomes are merged."""
    cols = list(families) + ["Other"]
    out = ["| order | " + " | ".join(cols) + " |", "|---|" + "---|" * len(cols)]
    seen: set[tuple[int, ...]] = set()
    for order in itertools.permutations(families):
        dist = Counter(next((f for f in order if f in c), "Other") for c in cats.values())
        key = tuple(dist[c] for c in cols)
        if key in seen:
            continue
        seen.add(key)
        out.append("| " + " > ".join(order) + " | " + " | ".join(str(dist[c]) for c in cols) + " |")
    return out


def report(configuration: Configuration) -> list[str]:
    """The Markdown report of one configuration."""
    families = configuration["families"]
    benchmark = load_benchmark_set(benchmark_set(configuration))
    paper_labels = benchmark["labels"]
    covered = benchmark_rows(benchmark, load_probes(configuration["results"]))
    cats = {k: set(r["categories"]) for k, r in covered.items()}
    verifier = f"{configuration['verifier']} + {configuration['solver']}"
    title = f"{verifier}, benchmark tasks ({len(paper_labels)})"
    out = [f"## {title}", ""]
    out.append(f"Tasks: {len(paper_labels)}; present in the recorded run: {len(covered)}.")
    missing = Counter(v for k, v in paper_labels.items() if k not in covered)
    if missing:
        out.append(
            "Absent tasks by paper label: "
            + ", ".join(f"{k} {v}" for k, v in sorted(missing.items()))
            + "."
        )
    out += [
        "",
        "Tasks by number of passing families: "
        + ", ".join(f"{n}: {c}" for n, c in sorted(Counter(len(c) for c in cats.values()).items())),
        "",
    ]
    out += [
        "Overlap matrix (diagonal: tasks the family repairs; off-diagonal: tasks both repair):",
        "",
    ]
    out += matrix(cats, families)
    out += ["", "Passing-family combinations:", ""]
    out += [
        f"- {' + '.join(c) if c else 'none'}: {n}"
        for c, n in Counter(tuple(sorted(c)) for c in cats.values()).most_common()
    ]
    out += [
        "",
        "Label distribution by family order (first passing family wins; distinct outcomes only):",
        "",
    ]
    out += order_table(cats, families)
    out += ["", "Paper label vs recorded label (paper order):", ""]
    cols = list(families) + ["Other"]
    conf = Counter((paper_labels[k], family(r["label"])) for k, r in covered.items())
    out += ["| paper \\ recorded | " + " | ".join(cols) + " |", "|---|" + "---|" * len(cols)]
    for p in cols:
        if any(conf[(p, q)] for q in cols):
            out.append(f"| {p} | " + " | ".join(str(conf[(p, q)]) for q in cols) + " |")
    return out + [""]


def main() -> None:
    """Print the reports as Markdown."""
    with_sets = [n for n, c in CONFIGURATIONS.items() if c["benchmark_set"] is not None]
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--configuration", choices=with_sets, action="append")
    args = parser.parse_args()
    for name in args.configuration or with_sets:
        print("\n".join(report(CONFIGURATIONS[name])))


if __name__ == "__main__":
    main()

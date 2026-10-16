"""Law-level view of the Verus AX probe on the 462 benchmark tasks.

The recorded Verus + Z3 run tries every sequence law on every essential
assertion (``axioms`` in ``probes.json`` lists all laws that restore
verification). Restricted to the Verus benchmark tasks, this script prints

* repairs per law, how often a law is the only one that repairs a task, and
  the split by corpus (CF-V vs VB);
* how the paper's labels decompose into law repairs and equality-seed repairs.

Usage::

    uv run python scripts/verus_laws.py
"""

from collections import Counter

from solver_needs.corpora import corpus_of_key
from solver_needs.labels import (
    CONFIGURATIONS,
    FAMILIES,
    benchmark_rows,
    benchmark_set,
    load_benchmark_set,
    load_probes,
)
from solver_needs.verus.laws import LAWS

LAW_ORDER = [
    "subrange-subrange",
    "subrange-full",
    "push-subrange",
    "subrange-push",
    "subrange-empty",
    "add-subrange",
    "split-concat",
    "add-empty",
    "add-assoc",
]


def eq_seed_passes(row: dict) -> bool:
    """Did an equality seed restore verification?"""
    return any(v == "pass" for v in (row.get("eq_seeds") or {}).values())


def law_table(rows: dict[str, dict]) -> list[str]:
    """Repairs per law, repairs by that law alone, and the split by corpus."""
    out = ["| Law | Repairs | Alone | CF-V | VB |", "|---|---|---|---|---|"]
    for law in LAW_ORDER:
        keys = [k for k, r in rows.items() if law in r["axioms"]]
        alone = sum(1 for k in keys if len(rows[k]["axioms"]) == 1)
        cf = sum(1 for k in keys if corpus_of_key(k) == "CF-V")
        out.append(f"| {law} | {len(keys)} | {alone} | {cf} | {len(keys) - cf} |")
    return out


def overlap_summary(labels: dict[str, str], rows: dict[str, dict]) -> list[str]:
    """How the law repairs overlap, and how each paper label splits into law and seed repairs."""
    repaired = {k for k, r in rows.items() if r["axioms"]}
    by_count = Counter(len(rows[k]["axioms"]) for k in repaired)
    combos = Counter(
        tuple(sorted(rows[k]["axioms"])) for k in repaired if len(rows[k]["axioms"]) > 1
    )
    out = [
        f"Repaired by at least one law: {len(repaired)}; by exactly one: {by_count[1]}; "
        f"by two or more: {len(repaired) - by_count[1]}.",
        "Most common combinations: "
        + "; ".join(f"{' + '.join(c)} ({n})" for c, n in combos.most_common(3))
        + ".",
        "Repaired by four or more laws: "
        + ", ".join(
            f"{k} ({labels[k]}, {len(rows[k]['axioms'])})"
            for k in sorted(repaired)
            if len(rows[k]["axioms"]) >= 4
        )
        + ".",
    ]
    for label in FAMILIES:
        keys = [k for k, lab in labels.items() if lab == label]
        law = sum(1 for k in keys if rows[k]["axioms"])
        both = sum(1 for k in keys if rows[k]["axioms"] and eq_seed_passes(rows[k]))
        seed_only = sum(1 for k in keys if not rows[k]["axioms"] and eq_seed_passes(rows[k]))
        out.append(
            f"Paper {label} ({len(keys)}): law {law}, law and equality seed {both}, "
            f"equality seed only {seed_only}."
        )
    return out


def main() -> None:
    """Print the law table and the overlap summary as Markdown."""
    configuration = CONFIGURATIONS["verus_z3"]
    benchmark = load_benchmark_set(benchmark_set(configuration))
    rows = benchmark_rows(benchmark, load_probes(configuration["results"]))
    assert set(LAW_ORDER) == set(LAWS)
    print(f"## Verus + Z3, benchmark tasks ({len(rows)}): repairs per law\n")
    print("\n".join(law_table(rows)))
    print()
    print("\n".join(overlap_summary({k: benchmark["labels"][k] for k in rows}, rows)))


if __name__ == "__main__":
    main()

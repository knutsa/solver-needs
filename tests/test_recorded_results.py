"""The recorded datasets, results and benchmark sets are consistent with each other and the code."""

import json
from collections import Counter

import pytest

from solver_needs import config
from solver_needs.corpora import KEY_PREFIX, corpus_of_key, dafny_sources, verus_sources
from solver_needs.dafny import classify as dafny_classify
from solver_needs.dafny.laws import LAWS as DAFNY_LAWS
from solver_needs.labels import (
    CONFIGURATIONS,
    benchmark_set,
    family,
    load_benchmark_set,
    load_dataset,
    load_labels,
    load_probes,
)
from solver_needs.verus import classify as verus_classify
from solver_needs.verus.laws import LAWS as VERUS_LAWS


@pytest.mark.parametrize("name", list(CONFIGURATIONS))
def test_results_cover_the_dataset(name):
    configuration = CONFIGURATIONS[name]
    dataset = load_dataset(configuration["dataset"])
    labels = load_labels(configuration["results"])
    probes = load_probes(configuration["results"])
    keys = [a["key"] for a in dataset["assertions"]]
    assert len(keys) == len(set(keys)) == dataset["counts"]["essential"]
    assert set(labels) == set(keys) == set(probes)
    for a in dataset["assertions"]:
        assert a["corpus"] in configuration["corpora"]
        assert corpus_of_key(a["key"]) == a["corpus"]
        assert a["key"].startswith(KEY_PREFIX[a["corpus"]] + "-")
        source = (config.ROOT / a["source_path"]).read_text().split("\n")
        assert "assert" in source[a["line"] - 1]


@pytest.mark.parametrize("name", list(CONFIGURATIONS))
def test_labels_follow_the_probe_order(name):
    configuration = CONFIGURATIONS[name]
    dafny = configuration["verifier"] == "Dafny"
    classifier = dafny_classify if dafny else verus_classify
    for key, row in load_probes(configuration["results"]).items():
        assert row["categories"] == classifier.Probe.categories(row)
        assert set(row["categories"]) <= set(configuration["families"])
        expected = next((f for f in classifier.ORDER if f in row["categories"]), "Other")
        assert family(row["label"]) == expected, key
        laws = row["prelude_axioms"] if dafny else row["axioms"]
        assert set(laws) <= set(DAFNY_LAWS if dafny else VERUS_LAWS)


def test_recorded_totals():
    counts = {
        n: Counter(family(v) for v in load_labels(c["results"]).values())
        for n, c in CONFIGURATIONS.items()
    }
    assert counts["dafny_z3"] == {"AX": 174, "INST": 156, "Other": 56}
    assert counts["dafny_cvc5"] == {"AX": 69, "INST": 82, "Other": 70}
    assert counts["verus_z3"] == {"AX": 176, "INST": 80, "NLA": 104, "FUEL": 26, "Other": 82}
    assert counts["verus_cvc5"] == {"AX": 143, "INST": 54, "FUEL": 24, "Other": 60}


def test_benchmark_sets():
    dafny = load_benchmark_set(benchmark_set(CONFIGURATIONS["dafny_z3"]))
    verus = load_benchmark_set(benchmark_set(CONFIGURATIONS["verus_z3"]))
    assert Counter(dafny["labels"].values()) == {"AX": 156, "INST": 133, "Other": 31}
    assert Counter(verus["labels"].values()) == {
        "AX": 173,
        "INST": 128,
        "NLA": 107,
        "FUEL": 26,
        "Other": 28,
    }
    for benchmark in (dafny, verus):
        assert set(benchmark["fine_labels"]) == set(benchmark["labels"])
        for key, fine in benchmark["fine_labels"].items():
            assert family(fine) == benchmark["labels"][key]
    assert set(verus["labels"]) <= set(load_labels(CONFIGURATIONS["verus_z3"]["results"]))
    recorded = set(load_labels(CONFIGURATIONS["dafny_z3"]["results"]))
    present = [k for k in dafny["labels"] if dafny["aliases"].get(k, k) in recorded]
    assert len(present) == 306


def test_corpora_match_the_datasets():
    dafny = {p for _, p, _ in dafny_sources()}
    verus = {p for _, p, _ in verus_sources()}
    for name, configuration in CONFIGURATIONS.items():
        programs = {p["problem"] for p in load_dataset(configuration["dataset"])["programs"]}
        if configuration["verifier"] == "Dafny":
            assert programs <= dafny, name
        else:
            assert programs == verus, name
    assert len(dafny) == 108 + 785
    manifest = json.loads((config.CORPORA / "DB" / "MANIFEST.json").read_text())
    assert manifest["programs"] == 785

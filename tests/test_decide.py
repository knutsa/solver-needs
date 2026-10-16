"""The label decision of the Dafny and Verus classifiers from stored probe evidence."""

from pathlib import Path

import pytest

from solver_needs import config
from solver_needs.dafny import classify as dafny_classify
from solver_needs.dafny.verify import DafnySettings
from solver_needs.verus import classify as verus_classify
from solver_needs.verus.verify import VerusSettings

DAFNY_SRC = """\
lemma L(s: seq<int>)
  requires |s| > 1
  ensures exists k :: 0 <= k < |s| && s[k] == s[k]
{
  assert s[..1] == [s[0]];
}
"""
VERUS_SRC = """\
use vstd::prelude::*;
verus! {
proof fn l(s: Seq<int>)
    requires s.len() > 1,
    ensures s.subrange(0, 1) =~= seq![s[0]],
{
    assert(s.subrange(0, 1) =~= seq![s[0]]);
}
}
"""


def dafny_evidence(seeds="fail", eq="fail", preludes=(), collection=True):
    return {
        "seeds": {"s[0]": seeds},
        "eq_seeds": {"s[..1] == [s[0]]": eq},
        "prelude_axioms": list(preludes),
        "shape": {"collection_eq": collection},
    }


@pytest.fixture
def dafny_probe(tmp_path, monkeypatch):
    (tmp_path / "p.dfy").write_text(DAFNY_SRC)
    monkeypatch.setattr(config, "ROOT", tmp_path)
    row = {"key": "T-1", "source_path": "p.dfy", "line": 5, "removal_errors": []}
    return dafny_classify.Probe(row, {}, tmp_path, DafnySettings.for_solver("z3"))


def test_dafny_categories_record_every_passing_probe(dafny_probe):
    r = dafny_evidence(seeds="pass", preludes=["take-full"])
    assert dafny_probe.decide(r) == "INST-forall"
    assert r["categories"] == ["INST", "AX"]


def test_dafny_collection_equality_seed_is_ax_and_other_is_inst(dafny_probe):
    assert dafny_probe.decide(dafny_evidence(eq="pass", collection=True)) == "AX"
    assert dafny_probe.decide(dafny_evidence(eq="pass", collection=False)) == "INST-forall"


def test_dafny_nothing_passing_is_other(dafny_probe):
    r = dafny_evidence()
    assert dafny_probe.decide(r) == "Other"
    assert r["categories"] == []


def test_dafny_witness_from_removal_errors(dafny_probe):
    dafny_probe.row["removal_errors"] = [{"line": 3, "message": "postcondition might not hold"}]
    assert dafny_probe.decide(dafny_evidence(seeds="pass")) == "INST-witness"


@pytest.fixture
def verus_probe(tmp_path, monkeypatch):
    (tmp_path / "p.rs").write_text(VERUS_SRC)
    monkeypatch.setattr(config, "ROOT", tmp_path)
    row = {"key": "V-1", "source_path": "p.rs", "line": 7, "removal_error": {}}
    return verus_classify.Probe(row, Path(tmp_path), VerusSettings("z3"))


def verus_evidence(**kw):
    r = {
        "fuel": {},
        "bridge": None,
        "seeds": {},
        "eq_seeds": {},
        "axioms": [],
        "nla": "fail",
        "shape": {"collection_eq": True},
    }
    r.update(kw)
    return r


def test_verus_paper_order(verus_probe):
    r = verus_evidence(fuel={"f": "pass"}, axioms=["add-empty"], nla="pass")
    assert verus_probe.decide(r) == "FUEL"
    assert r["categories"] == ["FUEL", "AX", "NLA"]


def test_verus_bridge_is_inst_forall(verus_probe):
    assert verus_probe.decide(verus_evidence(bridge="pass")) == "INST-forall"


def test_verus_other(verus_probe):
    assert verus_probe.decide(verus_evidence()) == "Other"

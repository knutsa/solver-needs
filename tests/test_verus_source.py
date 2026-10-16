"""Solver-free parts of the Verus extractor and classifier."""

from solver_needs.dafny.source import strip_comments
from solver_needs.verus import source
from solver_needs.verus.extract import carry_over_keys
from solver_needs.verus.verify import error_lines, file_status, probe_status, status_within

SRC = """\
use vstd::prelude::*;

verus! {

spec fn f(x: int) -> int { x + 1 }

proof fn lemma_a(s: Seq<int>)
    ensures s.len() >= 0,
{
    assert(s.len() >= 0);
    assert forall|i: int| 0 <= i < s.len() implies f(s[i]) > s[i] by {
        assert(f(s[i]) == s[i] + 1);
    }
    // assert(this is a comment);
    assert(1 + 1 == 2) by(nonlinear_arith);
}

pub fn exec_b(v: &Vec<u64>) -> (r: u64)
    ensures r == 0,
{
    proof { assert(v@.len() >= 0); }
    0
}

} // verus!

fn main() {
    assert!(exec_b(&vec![]) == 0);
}
"""

RLIMIT_MESSAGE = (
    "function body check: Resource limit (rlimit) exceeded; "
    "consider rerunning with --profile for more details"
)
VERUS_FAIL = f"""\
verification results:: 3 verified, 2 errors
error: assertion failed
  --> /tmp/x.rs:12:5
   |
12 |     assert(s.len() > 0);
   |     ^^^^^^^^^^^^^^^^^^^ assertion failed
note: recommendation not met
  --> /tmp/x.rs:40:9
   |
error: {RLIMIT_MESSAGE}
  --> /tmp/x.rs:30:1
   |
"""
VERUS_PASS = "verification results:: 5 verified, 0 errors\n"
VERUS_COMPILE = (
    "error[E0308]: mismatched types\n  --> /tmp/x.rs:21:9\n\n"
    "error: aborting due to 1 previous error\n"
)


def test_finds_every_ghost_assert_and_no_macro_or_comment():
    texts = [SRC[b:e] for b, e in source.assert_statements(SRC)]
    assert texts == [
        "assert(s.len() >= 0);",
        "assert forall|i: int| 0 <= i < s.len() implies f(s[i]) > s[i] by {\n"
        "        assert(f(s[i]) == s[i] + 1);\n    }",
        "assert(f(s[i]) == s[i] + 1);",
        "assert(1 + 1 == 2) by(nonlinear_arith);",
        "assert(v@.len() >= 0);",
    ]


def test_split_assert_kinds():
    plain = source.split_assert("assert(1 + 1 == 2) by(nonlinear_arith);")
    assert plain == {
        "kind": "plain",
        "expr": "1 + 1 == 2",
        "by_body": None,
        "tactic": "nonlinear_arith",
    }
    forall = source.split_assert("assert forall|i: int| p(i) implies q(i) by {\n assert(q(i));\n}")
    assert forall["kind"] == "forall"
    assert forall["expr"] == "forall|i: int| p(i) implies q(i)"
    assert source.inner_assert_exprs(forall["by_body"]) == ["q(i)"]


def test_terms_and_shape():
    masked, table = source.mask_generics("Seq::<int>::empty().add(s) =~= s.subrange(0, 1)")
    first = source.candidate_terms(masked)[0]
    assert first == "Seq__G0__::empty().add(s)"
    assert source.unmask(first, table) == "Seq::<int>::empty().add(s)"
    assert source.equality_atoms("a =~= b")[0][0] == "=~="
    assert source.shape_from_text("s.subrange(0, 1) == t", None)["collection_eq"]
    assert not source.shape_from_text("x == y", None)["collection_eq"]
    assert source.shape_from_text("x * y == z", None)["nonlinear"]
    recursive = "spec fn sum(s: Seq<int>) -> int decreases s.len() { 0 }"
    assert source.recursive_spec_fns(recursive) == {"sum"}


def test_enclosing_fn():
    clean = strip_comments(SRC)
    assert source.enclosing_fn_lines(clean, SRC.index("assert(s.len() >= 0)")) == (7, 17)
    first, last = source.enclosing_fn_lines(clean, SRC.index("assert!(exec_b"))
    assert (first, last) == (27, SRC.count("\n") + 1)
    assert source.enclosing_fn_lines(clean, SRC.index("assert(v@.len()")) == (18, 26)
    assert source.in_proof_context(SRC, SRC.index("assert(s.len() >= 0)"))
    assert not source.in_proof_context(SRC, SRC.index("0\n}"))


def test_verus_output_parsing():
    assert error_lines(VERUS_FAIL) == [(12, "assertion failed"), (30, RLIMIT_MESSAGE)]
    assert status_within("fail", VERUS_FAIL, (10, 20)) == ("fail", 1)
    assert status_within("fail", VERUS_FAIL, (25, 35)) == ("timeout", 1)
    assert status_within("fail", VERUS_FAIL, (50, 60)) == ("pass", 2)
    assert status_within("invalid", VERUS_COMPILE, (1, 5)) == ("invalid", 0)
    assert status_within("wall-timeout", "", (1, 5)) == ("wall-timeout", 0)
    assert file_status(VERUS_PASS) == "pass"
    assert file_status(VERUS_FAIL) == "fail"
    assert file_status(VERUS_COMPILE) == "invalid"
    assert file_status(None) == "wall-timeout"
    assert probe_status(VERUS_PASS)[0] == "pass"
    assert probe_status(VERUS_FAIL)[0] == "timeout"
    assert probe_status(None)[0] == "timeout"


def test_carry_over_keys_then_fresh():
    previous = [
        {"key": "V-7", "corpus": "CF-V", "problem": "p1", "line": 10, "text": "assert(a == b);"},
        {"key": "VB-2", "corpus": "VB", "problem": "MBPP/t", "line": 5, "text": "assert(x);"},
        {"key": "V-303", "corpus": "CF-V", "problem": "p1", "line": 20, "text": "assert(c);"},
    ]
    rows = [
        {"corpus": "CF-V", "problem": "p1", "line": 11, "text": "assert( a==b );"},
        {"corpus": "VB", "problem": "MBPP/t", "line": 5, "text": "assert(x);"},
        {"corpus": "CF-V", "problem": "p1", "line": 20, "text": "assert(c);"},
        {"corpus": "CF-V", "problem": "p1", "line": 30, "text": "assert(d);"},
        {"corpus": "VB", "problem": "MBPP/t", "line": 9, "text": "assert(y);"},
    ]
    carry_over_keys(rows, previous)
    assert [r["key"] for r in rows] == ["V-7", "VB-2", "V-303", "V-304", "VB-3"]
    assert [r["new_key"] for r in rows] == [False, False, False, True, True]

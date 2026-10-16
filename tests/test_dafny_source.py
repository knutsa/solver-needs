"""Solver-free parts of the Dafny extractor and classifier."""

from solver_needs.dafny import source
from solver_needs.dafny.extract import is_essential
from solver_needs.dafny.verify import errors_to_source_lines, parse_summary, status_within

SRC = """\
method M(s: seq<int>)
  requires |s| > 2
{
  assert s[..1] == [s[0]];
  assert L: s[1] == s[1];
  assert forall i :: 0 <= i < |s| ==> s[i] == s[i];
  assert {:split_here} s[2] == s[2];
  assert s[..2] == s[..1] + [s[1]] by {
    assert s[..1] == [s[0]];
  }
  reveal L;
}
"""


def test_labelled_asserts_are_detected():
    assert source.is_labelled("assert L: s[1] == s[1];")
    assert source.is_labelled("assert {:split_here} Lbl : x == 1;")
    assert source.is_labelled("assert 0: f(a, f(b, c)) == f(f(a, b), c) by { A(); }")
    for stmt in (
        "assert s[..1] == [s[0]];",
        "assert forall i :: 0 <= i < |s| ==> s[i] == s[i];",
        "assert {:split_here} s[2] == s[2];",
        "assert x :| P(x);",
        "assert m[k := v] == m;",
    ):
        assert not source.is_labelled(stmt), stmt


def test_every_statement_position_assert_is_a_candidate():
    spans = source.assert_statements(SRC)
    texts = [SRC[b:e] for b, e in spans]
    assert len(texts) == 6
    assert texts[4].startswith("assert s[..2]") and texts[4].endswith("}")
    assert texts[5] == "assert s[..1] == [s[0]];"
    kept = [t for t in texts if not source.is_labelled(t)]
    assert len(kept) == 5


def test_split_assert_and_inner_exprs():
    stmt = "assert s[..2] == s[..1] + [s[1]] by {\n  assert s[..1] == [s[0]];\n}"
    expr, body = source.split_assert(stmt)
    assert expr == "s[..2] == s[..1] + [s[1]]"
    assert body is not None
    assert source.inner_assert_exprs(body) == ["s[..1] == [s[0]]"]
    assert source.split_assert("assert {:split_here} s[2] == s[2];") == ("s[2] == s[2]", None)


def test_candidate_terms_and_equality_atoms():
    terms = source.candidate_terms("|s| > 0 ==> f(s[1..], n) + 1 == g(n)")
    assert terms == ["|s|", "f(s[1..], n) + 1", "f(s[1..], n)", "s[1..]", "g(n)"]
    assert source.candidate_terms("forall i :: P(s[i])") == []
    assert source.candidate_terms("x in S && y !in T") == ["x in S", "y !in T"]
    assert source.equality_atoms("a == b && c <= d ==> e == f") == ["a == b", "e == f"]


def test_enclosing_declaration():
    clean = source.strip_comments(SRC)
    assert source.enclosing_decl_lines(clean, SRC.index("assert L")) == (1, SRC.count("\n") + 1)


def test_essential_decision():
    def outcome(removal, seed2, placebo):
        return {"removal": removal, "removal_seed2": seed2, "placebo": placebo}

    assert is_essential(outcome("fail", "fail", "fail"))
    assert is_essential(outcome("timeout", "wall-timeout", "fail"))
    assert not is_essential(outcome("pass", None, None))
    assert not is_essential(outcome("invalid", None, None))
    assert not is_essential(outcome("fail", "pass", "fail"))
    assert not is_essential(outcome("fail", "fail", "pass"))


def test_error_lines_after_the_removed_statement_shift():
    errors = [
        {"line": 3, "message": "a", "related_line": None, "related_lines": []},
        {"line": 8, "message": "b", "related_line": 9, "related_lines": [9, 10]},
    ]
    mapped = errors_to_source_lines(errors, removed_newlines=2, start_line=5)
    assert mapped[0]["line"] == 3
    assert mapped[1]["line"] == 10
    assert mapped[1]["related_line"] == 11
    assert mapped[1]["related_lines"] == [11, 12]
    assert errors[1]["line"] == 8


def test_parse_summary_reads_budget_outcomes():
    finished = "Dafny program verifier finished with "
    assert parse_summary(finished + "3 verified, 0 errors")[0] == "pass"
    assert parse_summary(finished + "2 verified, 1 error")[0] == "fail"
    assert parse_summary(finished + "2 verified, 0 errors, 1 out of resource")[0] == "timeout"
    assert parse_summary(finished + "2 verified, 0 errors, 1 inconclusive")[0] == "timeout"
    assert parse_summary("x.dfy(3,1): Error: resolution/type errors detected")[0] == "invalid"
    assert parse_summary("BadExprFromProver ... " + finished + "1 verified, 0 errors")[0] == "fail"


def test_status_within_declaration():
    out = "f.dfy(12,3): Error: a postcondition could not be proved\nf.dfy(40,3): Error: x\n"
    assert status_within("fail", out, (10, 20)) == ("fail", 1)
    assert status_within("fail", out, (50, 60)) == ("pass", 2)
    budget = "f.dfy(12,3): Error: Verification of 'M' timed out after 300 seconds\n"
    assert status_within("timeout", budget, (10, 20)) == ("timeout", 0)
    assert status_within("wall-timeout", "", (1, 5)) == ("wall-timeout", 0)

"""Placing the DB corpus from a DafnyBench checkout."""

import pytest

from solver_needs.dafny import dafnybench as db


def test_sanitize_matches_corpus_names():
    assert (
        db.sanitize("703FinalProject_tmp_tmpr_10rn4z_DP-GD")
        == "DB_703FinalProject_tmp_tmpr_10rn4z_DP-GD"
    )
    assert db.sanitize("a b+c") == "DB_a_b_c"
    assert len(db.sanitize("x" * 200)) == 123


def test_copies_every_program_verbatim(tmp_path):
    gt = tmp_path / "gt"
    gt.mkdir()
    (gt / "one.dfy").write_text("method M() { assert true; }\n")
    (gt / "two x.dfy").write_text("lemma L() {}\n")
    names = db.copy_ground_truth(gt, tmp_path / "out")
    assert names == {"DB_one": "one.dfy", "DB_two_x": "two x.dfy"}
    assert (tmp_path / "out" / "DB_two_x.dfy").read_text() == "lemma L() {}\n"


def test_existing_file_must_be_identical(tmp_path):
    gt = tmp_path / "gt"
    gt.mkdir()
    (gt / "one.dfy").write_text("method M() {}\n")
    out = tmp_path / "out"
    out.mkdir()
    (out / "DB_one.dfy").write_text("method M() {}\n")
    db.copy_ground_truth(gt, out)
    (out / "DB_one.dfy").write_text("method M() { assert true; }\n")
    with pytest.raises(SystemExit):
        db.copy_ground_truth(gt, out)


def test_name_collision_and_empty_dir_fail(tmp_path):
    gt = tmp_path / "gt"
    gt.mkdir()
    with pytest.raises(SystemExit):
        db.copy_ground_truth(gt, tmp_path / "out")
    (gt / "a b.dfy").write_text("")
    (gt / "a_b.dfy").write_text("")
    with pytest.raises(SystemExit):
        db.copy_ground_truth(gt, tmp_path / "out")

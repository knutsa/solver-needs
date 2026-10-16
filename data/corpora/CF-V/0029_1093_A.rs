use vstd::prelude::*;

verus! {

// Sum of a sequence of integers
pub open spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        sum_seq(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    }
}

// A valid dice face: the six-faced die has faces {2, 3, 4, 5, 6, 7}
pub open spec fn valid_dice_face(v: int) -> bool {
    2 <= v && v <= 7
}

// Every element in the sequence is a valid dice face
pub open spec fn all_valid_faces(dice: Seq<int>) -> bool {
    forall|i: int| 0 <= i < dice.len() ==> valid_dice_face(dice[i])
}

// Construct a concrete dice sequence achieving a target sum.
pub open spec fn build_dice_witness(extra: int, num_left: int) -> Seq<int>
    recommends num_left >= 0,
    decreases num_left,
{
    if num_left <= 0 {
        Seq::<int>::empty()
    } else if num_left == 1 {
        seq![2 + extra]
    } else {
        let add = if extra > 5 { 5int } else if extra < 0 { 0int } else { extra };
        seq![2 + add] + build_dice_witness(extra - add, num_left - 1)
    }
}

// Build a witness dice sequence for the given target and number of rolls
pub open spec fn dice_witness(target: int, num_rolls: int) -> Seq<int>
    recommends num_rolls >= 1,
{
    build_dice_witness(target - 2 * num_rolls, num_rolls)
}

// numRolls is a correct answer for target iff there exists a sequence of
// numRolls dice faces (each in {2..7}) whose sum equals target.
pub open spec fn is_correct_answer(target: int, num_rolls: int) -> bool {
    num_rolls >= 1 &&
    exists|dice: Seq<int>| dice.len() == num_rolls &&
        all_valid_faces(dice) &&
        sum_seq(dice) == target
}

// ========== Helper Lemmas ==========

proof fn sum_seq_singleton(v: int)
    ensures sum_seq(seq![v]) == v,
{
    let s = seq![v];
    assert(s.len() == 1);
    assert(s.subrange(0, 0) =~= Seq::<int>::empty());
    assert(sum_seq(s.subrange(0, 0)) == 0);
    assert(s[0] == v);
}

pub proof fn sum_seq_prepend(v: int, s: Seq<int>)
    ensures sum_seq(seq![v] + s) == v + sum_seq(s),
    decreases s.len(),
{
    let vs = seq![v] + s;
    if s.len() == 0 {
        assert(vs =~= seq![v]);
        sum_seq_singleton(v);
    } else {
        assert(vs.subrange(0, vs.len() - 1) =~= seq![v] + s.subrange(0, s.len() - 1));
        assert(vs[vs.len() - 1] == s[s.len() - 1]);
        sum_seq_prepend(v, s.subrange(0, s.len() - 1));
    }
}

pub proof fn build_dice_witness_length(extra: int, num_left: int)
    requires num_left >= 0,
    ensures build_dice_witness(extra, num_left).len() == num_left,
    decreases num_left,
{
    if num_left <= 1 {
    } else {
        let add = if extra > 5 { 5int } else if extra < 0 { 0int } else { extra };
        build_dice_witness_length(extra - add, num_left - 1);
        let rest = build_dice_witness(extra - add, num_left - 1);
        assert(build_dice_witness(extra, num_left) =~= seq![2 + add] + rest);
    }
}

proof fn extra_add_bound(extra: int, add: int, num_left: int)
    requires
        0 <= extra,
        extra <= 5 * num_left,
        num_left >= 2,
        add == (if extra > 5 { 5int } else if extra < 0 { 0int } else { extra }),
    ensures
        0 <= add <= 5,
        add <= extra,
        0 <= extra - add,
        extra - add <= 5 * (num_left - 1),
{
    assert(0 <= add <= 5);
    assert(add <= extra);
    assert(0 <= extra - add);
    if extra > 5 {
        assert(add == 5);
        assert(extra - 5 <= 5 * num_left - 5);
        assert(5 * num_left - 5 == 5 * (num_left - 1)) by(nonlinear_arith)
            requires num_left >= 2;
    } else {
        assert(add == extra);
        assert(extra - add == 0);
    }
}

pub proof fn build_dice_witness_valid(extra: int, num_left: int)
    requires
        num_left >= 0,
        0 <= extra <= 5 * num_left,
    ensures all_valid_faces(build_dice_witness(extra, num_left)),
    decreases num_left,
{
    if num_left == 0 {
    } else if num_left == 1 {
        let bw = build_dice_witness(extra, num_left);
        assert(bw =~= seq![2 + extra]);
        assert(valid_dice_face(bw[0]));
    } else {
        let add = if extra > 5 { 5int } else if extra < 0 { 0int } else { extra };
        extra_add_bound(extra, add, num_left);
        build_dice_witness_valid(extra - add, num_left - 1);
        build_dice_witness_length(extra - add, num_left - 1);
        let rest = build_dice_witness(extra - add, num_left - 1);
        assert(all_valid_faces(rest));
        assert(valid_dice_face(2 + add));
        let bw = build_dice_witness(extra, num_left);
        assert(bw =~= seq![2 + add] + rest);
        assert forall|j: int| 0 <= j < bw.len() implies valid_dice_face(bw[j]) by {
            if j == 0 {
                assert(bw[0] == 2 + add);
            } else {
                assert(bw[j] == rest[j - 1]);
            }
        }
    }
}

pub proof fn build_dice_witness_sum(extra: int, num_left: int)
    requires
        num_left >= 0,
        0 <= extra <= 5 * num_left,
    ensures sum_seq(build_dice_witness(extra, num_left)) == 2 * num_left + extra,
    decreases num_left,
{
    if num_left == 0 {
    } else if num_left == 1 {
        let bw = build_dice_witness(extra, num_left);
        assert(bw =~= seq![2 + extra]);
        sum_seq_singleton(2 + extra);
        assert(sum_seq(bw) == 2 + extra);
    } else {
        let add = if extra > 5 { 5int } else if extra < 0 { 0int } else { extra };
        extra_add_bound(extra, add, num_left);
        build_dice_witness_sum(extra - add, num_left - 1);
        let rest = build_dice_witness(extra - add, num_left - 1);
        assert(sum_seq(rest) == 2 * (num_left - 1) + (extra - add));
        sum_seq_prepend(2 + add, rest);
        assert(sum_seq(seq![2 + add] + rest) == (2 + add) + sum_seq(rest));
        assert(build_dice_witness(extra, num_left) =~= seq![2 + add] + rest);
    }
}

// Prove correctness: if 2*r <= val <= 7*r and r >= 1, then IsCorrectAnswer(val, r)
pub proof fn dice_rolling_correctness(val: int, r: int)
    requires
        r >= 1,
        2 * r <= val,
        val <= 7 * r,
    ensures is_correct_answer(val, r),
{
    let extra = val - 2 * r;
    assert(extra >= 0);
    assert(extra <= 5 * r) by(nonlinear_arith)
        requires val <= 7 * r, extra == val - 2 * r;
    build_dice_witness_length(extra, r);
    build_dice_witness_valid(extra, r);
    build_dice_witness_sum(extra, r);
    let dice = build_dice_witness(extra, r);
    assert(dice.len() == r);
    assert(all_valid_faces(dice));
    assert(sum_seq(dice) == val);
}

// ========== Method ==========

pub fn dice_rolling(x: &Vec<i64>) -> (rolls: Vec<i64>)
    requires forall|i: int| 0 <= i < x.len() ==> x[i] >= 2,
    ensures
        rolls.len() == x.len(),
        forall|i: int| 0 <= i < rolls.len() ==> is_correct_answer(x[i] as int, rolls[i] as int),
{
    let mut rolls: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            rolls.len() == i,
            forall|j: int| 0 <= j < i as int ==> is_correct_answer(x[j] as int, rolls[j] as int),
            forall|j: int| 0 <= j < x.len() ==> x[j] >= 2,
        decreases x.len() - i,
    {
        let val = x[i];
        let r: i64;
        if val <= 7 {
            r = 1;
            proof {
                dice_rolling_correctness(val as int, 1);
            }
        } else {
            if val % 7 != 0 {
                r = val / 7 + 1;
            } else {
                r = val / 7;
            }
            proof {
                let vv = val as int;
                let rr = r as int;
                if vv % 7 == 0 {
                    assert(rr == vv / 7);
                    assert(vv == 7 * rr) by(nonlinear_arith)
                        requires vv % 7 == 0, rr == vv / 7;
                    assert(2 * rr <= 7 * rr) by(nonlinear_arith)
                        requires rr >= 1;
                } else {
                    assert(rr == vv / 7 + 1);
                    assert(vv == 7 * (vv / 7) + vv % 7);
                    assert(7 * rr == 7 * (vv / 7) + 7) by(nonlinear_arith)
                        requires rr == vv / 7 + 1;
                    assert(vv % 7 >= 1);
                    assert(vv % 7 < 7);
                    assert(vv < 7 * rr);
                    assert(2 * rr <= vv) by(nonlinear_arith)
                        requires
                            vv > 7,
                            rr == vv / 7 + 1,
                            vv == 7 * (vv / 7) + vv % 7,
                            vv % 7 >= 1,
                    ;
                }
                dice_rolling_correctness(vv, rr);
            }
        }
        rolls.push(r);
        i = i + 1;
    }
    rolls
}

fn main() {}

} // verus!

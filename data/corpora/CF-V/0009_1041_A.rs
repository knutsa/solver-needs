use vstd::prelude::*;

verus! {

// ── Specification ──

pub open spec fn seq_min(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len()
    when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let rest = seq_min(a.take(a.len() as int - 1));
        if a[a.len() as int - 1] < rest { a[a.len() as int - 1] } else { rest }
    }
}

pub open spec fn seq_max(a: Seq<int>) -> int
    recommends a.len() > 0
    decreases a.len()
    when a.len() > 0
{
    if a.len() == 1 {
        a[0]
    } else {
        let rest = seq_max(a.take(a.len() as int - 1));
        if a[a.len() as int - 1] > rest { a[a.len() as int - 1] } else { rest }
    }
}

pub open spec fn valid_store_config(a: Seq<int>, start_id: int, total_before: int) -> bool {
    total_before >= a.len() &&
    forall|i: int| 0 <= i < a.len() ==> start_id <= #[trigger] a[i] < start_id + total_before
}

pub open spec fn feasible_stolen_count(a: Seq<int>, k: int) -> bool
    recommends a.len() > 0
{
    k >= 0 &&
    exists|x: int| #[trigger] valid_store_config(a, x, a.len() as int + k)
}

pub open spec fn min_stolen_count(a: Seq<int>, k: int) -> bool
    recommends a.len() > 0
{
    feasible_stolen_count(a, k) &&
    (k == 0 || !feasible_stolen_count(a, k - 1))
}

// ── Helper Lemmas ──

proof fn seq_min_is_min(a: Seq<int>)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> seq_min(a) <= #[trigger] a[i]
    decreases a.len()
{
    if a.len() > 1 {
        let prefix = a.take(a.len() as int - 1);
        seq_min_is_min(prefix);
        assert forall|i: int| 0 <= i < a.len() implies seq_min(a) <= #[trigger] a[i] by {
            if i < a.len() - 1 {
                assert(prefix[i] == a[i]);
            }
        };
    }
}

proof fn seq_max_is_max(a: Seq<int>)
    requires a.len() > 0
    ensures forall|i: int| 0 <= i < a.len() ==> seq_max(a) >= #[trigger] a[i]
    decreases a.len()
{
    if a.len() > 1 {
        let prefix = a.take(a.len() as int - 1);
        seq_max_is_max(prefix);
        assert forall|i: int| 0 <= i < a.len() implies seq_max(a) >= #[trigger] a[i] by {
            if i < a.len() - 1 {
                assert(prefix[i] == a[i]);
            }
        };
    }
}

proof fn seq_min_in_seq(a: Seq<int>)
    requires a.len() > 0
    ensures exists|i: int| 0 <= i < a.len() && #[trigger] a[i] == seq_min(a)
    decreases a.len()
{
    if a.len() == 1 {
        assert(a[0] == seq_min(a));
    } else {
        let prefix = a.take(a.len() as int - 1);
        seq_min_in_seq(prefix);
        let j = choose|j: int| 0 <= j < prefix.len() && #[trigger] prefix[j] == seq_min(prefix);
        let rest = seq_min(prefix);
        if a[a.len() as int - 1] < rest {
            assert(a[a.len() as int - 1] == seq_min(a));
        } else {
            assert(prefix[j] == a[j]);
            assert(a[j] == rest);
            assert(rest == seq_min(a));
        }
    }
}

proof fn seq_max_in_seq(a: Seq<int>)
    requires a.len() > 0
    ensures exists|i: int| 0 <= i < a.len() && #[trigger] a[i] == seq_max(a)
    decreases a.len()
{
    if a.len() == 1 {
        assert(a[0] == seq_max(a));
    } else {
        let prefix = a.take(a.len() as int - 1);
        seq_max_in_seq(prefix);
        let j = choose|j: int| 0 <= j < prefix.len() && #[trigger] prefix[j] == seq_max(prefix);
        let rest = seq_max(prefix);
        if a[a.len() as int - 1] > rest {
            assert(a[a.len() as int - 1] == seq_max(a));
        } else {
            assert(prefix[j] == a[j]);
            assert(a[j] == rest);
            assert(rest == seq_max(a));
        }
    }
}

proof fn feasibility_lemma(a: Seq<int>, lo: int, hi: int, k: int)
    requires
        a.len() > 0,
        k >= 0,
        lo == seq_min(a),
        hi == seq_max(a),
        hi - lo + 1 - a.len() as int <= k,
    ensures feasible_stolen_count(a, k)
{
    seq_min_is_min(a);
    seq_max_is_max(a);
    assert forall|i: int| 0 <= i < a.len() implies lo <= #[trigger] a[i] < lo + (a.len() as int + k) by {};
    assert(valid_store_config(a, lo, a.len() as int + k));
}

proof fn infeasibility_lemma(a: Seq<int>, k: int)
    requires
        a.len() > 0,
        0 <= k < seq_max(a) - seq_min(a) + 1 - a.len() as int,
    ensures !feasible_stolen_count(a, k)
{
    seq_min_in_seq(a);
    seq_max_in_seq(a);
    let lo = seq_min(a);
    let hi = seq_max(a);
    let jlo = choose|j: int| 0 <= j < a.len() && #[trigger] a[j] == lo;
    let jhi = choose|j: int| 0 <= j < a.len() && #[trigger] a[j] == hi;

    assert forall|x: int| !(#[trigger] valid_store_config(a, x, a.len() as int + k)) by {
        if valid_store_config(a, x, a.len() as int + k) {
            assert(x <= a[jlo]);
            assert(a[jhi] < x + (a.len() as int + k));
            assert(a.len() as int + k > hi - lo);
            assert(false);
        }
    };
    if feasible_stolen_count(a, k) {
        let x_witness = choose|x: int| #[trigger] valid_store_config(a, x, a.len() as int + k);
        assert(!valid_store_config(a, x_witness, a.len() as int + k));
        assert(false);
    }
}

// ── Implementation ──

// Precondition: all values in [0, i64::MAX/2] so arithmetic doesn't overflow.
// This is a natural constraint for keyboard IDs.
fn heist(a: &Vec<i64>) -> (stolen: i64)
    requires
        a@.len() > 0,
        a@.len() <= i64::MAX,
        forall|i: int| #![trigger a@[i]] 0 <= i < a@.len() ==> 0 <= a@[i] <= i64::MAX / 2,
    ensures
        stolen >= 0,
        min_stolen_count(a@.map(|_idx: int, v: i64| v as int), stolen as int),
{
    let ghost a_spec: Seq<int> = a@.map(|_idx: int, v: i64| v as int);

    let mut lo: i64 = a[0];
    let mut hi: i64 = a[0];
    let mut i: usize = 1;

    while i < a.len()
        invariant
            1 <= i <= a.len(),
            a@.len() > 0,
            a_spec =~= a@.map(|_idx: int, v: i64| v as int),
            lo as int == seq_min(a_spec.take(i as int)),
            hi as int == seq_max(a_spec.take(i as int)),
            0 <= lo <= i64::MAX / 2,
            0 <= hi <= i64::MAX / 2,
            a@.len() <= i64::MAX,
            forall|j: int| #![trigger a@[j]] 0 <= j < a@.len() ==> 0 <= a@[j] <= i64::MAX / 2,
        decreases a.len() - i,
    {
        proof {
            assert(a_spec.take(i as int + 1).take(i as int) =~= a_spec.take(i as int));
            assert(a_spec.take(i as int + 1)[i as int] == a_spec[i as int]);
        }
        if a[i] < lo {
            lo = a[i];
        }
        if a[i] > hi {
            hi = a[i];
        }
        i = i + 1;
    }

    proof {
        assert(a_spec.take(a_spec.len() as int) =~= a_spec);
    }

    // hi, lo in [0, i64::MAX/2], so hi - lo in [0, i64::MAX/2], no overflow
    let span: i64 = hi - lo;
    // span + 1 <= i64::MAX/2 + 1, fits in i64
    let span_plus_1: i64 = span + 1;
    // a.len() fits in i64 since it's a usize and we need len <= i64::MAX
    let len_i64: i64 = a.len() as i64;
    // span_plus_1 - len_i64: span_plus_1 <= i64::MAX/2+1 and len_i64 >= 1
    // Result >= -(len_i64) >= -i64::MAX > i64::MIN, and <= span_plus_1 <= i64::MAX/2+1 < i64::MAX
    let res: i64 = span_plus_1 - len_i64;

    if res <= 0 {
        proof {
            feasibility_lemma(a_spec, lo as int, hi as int, 0);
        }
        return 0;
    }

    proof {
        // res > 0, so hi - lo + 1 > |a|, meaning hi - lo + 1 - |a| > 0
        // We need to show res as int == hi as int - lo as int + 1 - a_spec.len()
        assert(res as int == hi as int - lo as int + 1 - a_spec.len() as int);
        feasibility_lemma(a_spec, lo as int, hi as int, res as int);
        // For infeasibility: need 0 <= res-1 < seq_max - seq_min + 1 - |a|
        // res - 1 = hi - lo + 1 - |a| - 1 = hi - lo - |a|
        // seq_max - seq_min + 1 - |a| = hi - lo + 1 - |a| = res
        // So res - 1 < res. Check.
        infeasibility_lemma(a_spec, res as int - 1);
    }
    res
}

} // verus!

fn main() {}

use vstd::prelude::*;

verus! {

// Number of adjacent pairs: (1,2), (3,4), ..., (10^9-1, 10^9)
pub spec const NUM_PAIRS: nat = 500000000;

// A single replacement operation: replace `from` with `to` applied to one value.
pub open spec fn replace_val(v: int, from: int, to: int) -> int {
    if v == from { to } else { v }
}

// Apply pair k of Mishka's algorithm to a single value.
// Pair k: step 2k-1 replaces (2k-1) with 2k, step 2k replaces 2k with (2k-1).
pub open spec fn apply_pair_to_val(v: int, k: nat) -> int
    recommends k >= 1
{
    replace_val(replace_val(v, 2 * (k as int) - 1, 2 * (k as int)), 2 * (k as int), 2 * (k as int) - 1)
}

// Apply pairs lo through hi (inclusive) to value v, in sequential order.
pub open spec fn apply_pairs_range(v: int, lo: nat, hi: nat) -> int
    recommends 1 <= lo <= hi
    decreases hi - lo
{
    if v < 2 * (lo as int) - 1 || v > 2 * (hi as int) {
        v
    } else if lo == hi {
        apply_pair_to_val(v, lo)
    } else {
        let mid: int = (lo as int) + ((hi as int) - (lo as int)) / 2;
        apply_pairs_range(apply_pairs_range(v, lo, mid as nat), (mid + 1) as nat, hi)
    }
}

// The complete Mishka algorithm on a single value.
pub open spec fn mishka_algorithm(v: int) -> int
    recommends 1 <= v <= 2 * (NUM_PAIRS as int)
{
    apply_pairs_range(v, 1, NUM_PAIRS)
}

// b is the correct output of Mishka's algorithm applied element-wise to a.
pub open spec fn is_correct_result(a: Seq<int>, b: Seq<int>) -> bool
    recommends forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1000000000
{
    b.len() == a.len() &&
    forall|i: int| 0 <= i < a.len() ==> #[trigger] b[i] == mishka_algorithm(#[trigger] a[i])
}

// Key lemma: ApplyPairsRange either makes an even value odd (v-1) or leaves odd values unchanged.
pub proof fn apply_pairs_range_lemma(v: int, lo: nat, hi: nat)
    requires 1 <= lo <= hi,
    ensures apply_pairs_range(v, lo, hi) ==
        if (v % 2 == 0 && v >= 2 * (lo as int) - 1 && v <= 2 * (hi as int)) { (v - 1) as int } else { v },
    decreases hi - lo,
{
    if v < 2 * (lo as int) - 1 || v > 2 * (hi as int) {
        // trivial
    } else if lo == hi {
        // base case: single pair
    } else {
        let mid: int = (lo as int) + ((hi as int) - (lo as int)) / 2;
        apply_pairs_range_lemma(v, lo, mid as nat);
        let v1 = apply_pairs_range(v, lo, mid as nat);
        apply_pairs_range_lemma(v1, (mid + 1) as nat, hi);
    }
}

pub fn adjacent_replacements(a: &Vec<i64>) -> (b: Vec<i64>)
    requires
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1000000000,
    ensures
        b@.len() == a@.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] b@[i] == mishka_algorithm(a@[i] as int),
{
    let mut b: Vec<i64> = Vec::new();
    for idx in 0..a.len()
        invariant
            b@.len() == idx,
            forall|j: int| 0 <= j < idx ==> #[trigger] b@[j] == mishka_algorithm(a@[j] as int),
            forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1000000000,
    {
        let ai: i64 = a[idx];
        proof {
            apply_pairs_range_lemma(ai as int, 1, NUM_PAIRS);
            assert(mishka_algorithm(ai as int) == if ai as int % 2 == 0 { (ai - 1) as int } else { ai as int });
        }
        if ai % 2 == 0 {
            b.push(ai - 1);
        } else {
            b.push(ai);
        }
    }
    b
}

fn main() {}

} // verus!

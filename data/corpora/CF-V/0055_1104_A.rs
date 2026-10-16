use vstd::prelude::*;

verus! {

// === Specification predicates and functions ===

pub open spec fn sum(a: Seq<int>) -> int
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        a[a.len() - 1] + sum(a.subrange(0, a.len() - 1))
    }
}

pub open spec fn all_in_range(a: Seq<int>, lo: int, hi: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> lo <= #[trigger] a[i] && a[i] <= hi
}

pub open spec fn distinct_set(a: Seq<int>) -> Set<int>
    decreases a.len(),
{
    if a.len() == 0 {
        Set::empty()
    } else {
        Set::empty().insert(a[a.len() - 1]).union(distinct_set(a.subrange(0, a.len() - 1)))
    }
}

pub open spec fn count_distinct(a: Seq<int>) -> int {
    distinct_set(a).len() as int
}

// A valid splitting of n: non-empty sequence of digits 1..9 summing to n
pub open spec fn is_valid_splitting(a: Seq<int>, n: int) -> bool {
    a.len() >= 1 && all_in_range(a, 1, 9) && sum(a) == n
}

pub open spec fn pow2(e: int) -> int
    decreases e,
{
    if e <= 0 {
        1
    } else {
        2 * pow2(e - 1)
    }
}

pub open spec fn pop_count(mask: int) -> int
    decreases mask,
{
    if mask <= 0 {
        0
    } else {
        pop_count(mask / 2) + mask % 2
    }
}

// Can n be expressed as a non-negative integer combination of the
// digit values v..9 whose bits are set in mask?
pub open spec fn can_make_sum_from(n: int, mask: int, v: int) -> bool
    decreases 10 - v,
{
    if v >= 10 {
        n == 0
    } else if (mask / pow2(v - 1)) % 2 == 0 {
        can_make_sum_from(n, mask, v + 1)
    } else {
        exists|c: int| 0 <= c <= n / v && #[trigger] can_make_sum_from(n - c * v, mask, v + 1)
    }
}

pub open spec fn can_make_sum(n: int, mask: int) -> bool {
    can_make_sum_from(n, mask, 1)
}

pub open spec fn can_split_with_at_most(n: int, d: int) -> bool {
    exists|mask: int| 0 <= mask < 512 && pop_count(mask) <= d && can_make_sum(n, mask)
}

// === Helper Lemmas ===

pub open spec fn ones_seq(n: int) -> Seq<int>
    decreases n,
{
    if n <= 0 {
        Seq::empty()
    } else {
        ones_seq(n - 1).push(1)
    }
}

proof fn ones_seq_len(n: int)
    requires n >= 0,
    ensures ones_seq(n).len() == n,
    decreases n,
{
    if n > 0 {
        ones_seq_len(n - 1);
    }
}

proof fn ones_seq_index(n: int, i: int)
    requires
        n >= 0,
        0 <= i < n,
    ensures
        ones_seq(n)[i] == 1,
    decreases n,
{
    ones_seq_len(n);
    if n > 0 {
        ones_seq_len(n - 1);
        if i < n - 1 {
            ones_seq_index(n - 1, i);
        }
    }
}

proof fn ones_seq_subrange(n: int)
    requires n >= 1,
    ensures ones_seq(n).subrange(0, n as int - 1) =~= ones_seq(n - 1),
    decreases n,
{
    ones_seq_len(n);
    ones_seq_len(n - 1);
    // Both have same length: n-1
    // For each index i in 0..n-1:
    //   ones_seq(n).subrange(0, n-1)[i] == ones_seq(n)[i] == 1
    //   ones_seq(n-1)[i] == 1
    assert forall|i: int| 0 <= i < n - 1 implies #[trigger] ones_seq(n).subrange(0, n as int - 1)[i] == ones_seq(n - 1)[i] by {
        ones_seq_index(n, i);
        ones_seq_index(n - 1, i);
    }
}

proof fn sum_ones(n: int)
    requires n >= 0,
    ensures sum(ones_seq(n)) == n,
    decreases n,
{
    ones_seq_len(n);
    if n > 0 {
        ones_seq_len(n - 1);
        ones_seq_index(n, n - 1);
        // sum(ones_seq(n)) = ones_seq(n)[n-1] + sum(ones_seq(n).subrange(0, n-1))
        //                   = 1 + sum(ones_seq(n-1))
        ones_seq_subrange(n);
        assert(ones_seq(n).subrange(0, ones_seq(n).len() - 1) =~= ones_seq(n - 1));
        sum_ones(n - 1);
    }
}

proof fn distinct_set_ones(n: int)
    requires n >= 1,
    ensures distinct_set(ones_seq(n)) =~= Set::empty().insert(1),
    decreases n,
{
    ones_seq_len(n);
    ones_seq_index(n, n - 1);
    if n == 1 {
        ones_seq_len(0);
        ones_seq_len(1);
        ones_seq_subrange(1);
        assert(ones_seq(1).subrange(0, 0) =~= ones_seq(0));
        assert(ones_seq(0) =~= Seq::<int>::empty());
        assert(distinct_set(Seq::<int>::empty()) =~= Set::<int>::empty());
        assert(ones_seq(1).subrange(0, ones_seq(1).len() - 1) =~= Seq::<int>::empty());
        // distinct_set(ones_seq(1)) = {ones_seq(1)[0]} union distinct_set(empty) = {1} union {} = {1}
        assert(ones_seq(1)[ones_seq(1).len() - 1] == 1);
        assert(Set::<int>::empty().insert(1).union(Set::<int>::empty()) =~= Set::<int>::empty().insert(1));
    } else {
        ones_seq_subrange(n);
        ones_seq_len(n);
        ones_seq_len(n - 1);
        assert(ones_seq(n).subrange(0, ones_seq(n).len() - 1) =~= ones_seq(n - 1));
        distinct_set_ones(n - 1);
        assert(distinct_set(ones_seq(n - 1)) =~= Set::<int>::empty().insert(1));
        assert(ones_seq(n)[ones_seq(n).len() - 1] == 1);
        assert(Set::<int>::empty().insert(1).union(Set::<int>::empty().insert(1)) =~= Set::<int>::empty().insert(1));
    }
}

proof fn pow2_positive(e: int)
    requires e >= 0,
    ensures pow2(e) >= 1,
    decreases e,
{
    if e > 0 {
        pow2_positive(e - 1);
    }
}

proof fn pop_count_nonneg(mask: int)
    requires mask >= 0,
    ensures pop_count(mask) >= 0,
    decreases mask,
{
    if mask > 0 {
        pop_count_nonneg(mask / 2);
    }
}

proof fn pop_count_zero_implies_mask_zero(mask: int)
    requires mask >= 0,
    ensures pop_count(mask) == 0 ==> mask == 0,
    decreases mask,
{
    if mask > 0 {
        pop_count_zero_implies_mask_zero(mask / 2);
        pop_count_nonneg(mask / 2);
    }
}

proof fn cannot_make_positive_sum_from_zero_mask(n: int, v: int)
    requires
        n >= 1,
        1 <= v <= 10,
    ensures
        !can_make_sum_from(n, 0, v),
    decreases 10 - v,
{
    if v < 10 {
        // Need to show (0 / pow2(v-1)) % 2 == 0
        // We'll case-split on v to unfold pow2 concretely
        cannot_make_positive_sum_from_zero_mask_helper(n, v);
        cannot_make_positive_sum_from_zero_mask(n, v + 1);
    }
}

proof fn cannot_make_positive_sum_from_zero_mask_helper(n: int, v: int)
    requires
        n >= 1,
        1 <= v <= 9,
    ensures
        (0int / pow2(v - 1)) % 2 == 0,
{
    // v ranges from 1 to 9, so v-1 ranges from 0 to 8
    // pow2(0)=1, pow2(1)=2, ..., pow2(8)=256
    // 0 / any_positive == 0, 0 % 2 == 0
    reveal_with_fuel(pow2, 10);
    // Now pow2 is unfolded enough that the solver sees concrete values
}

proof fn cannot_split_with_zero_distinct(n: int)
    requires n >= 1,
    ensures !can_split_with_at_most(n, 0),
{
    assert forall|mask: int| 0 <= mask < 512 implies !(pop_count(mask) <= 0 && can_make_sum(n, mask)) by {
        if pop_count(mask) <= 0 {
            pop_count_nonneg(mask);
            pop_count_zero_implies_mask_zero(mask);
            cannot_make_positive_sum_from_zero_mask(n, 1);
        }
    }
}

// === Method with formal specification ===

fn split_into_digits(n: i64) -> (result: (i64, Vec<i64>))
    requires
        n >= 1,
        n <= i64::MAX,
    ensures
        result.0 == result.1.len(),
        is_valid_splitting(result.1@.map_values(|v: i64| v as int), n as int),
        !can_split_with_at_most(n as int, count_distinct(result.1@.map_values(|v: i64| v as int)) - 1),
{
    let mut digits: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < n
        invariant
            0 <= i <= n,
            digits.len() == i,
            forall|k: int| 0 <= k < digits.len() ==> digits@[k] == 1i64,
            n <= i64::MAX,
        decreases n - i,
    {
        digits.push(1);
        i = i + 1;
    }

    let ghost digits_spec: Seq<int> = digits@.map_values(|v: i64| v as int);

    proof {
        // Show digits_spec =~= ones_seq(n)
        ones_seq_len(n as int);
        assert(digits_spec.len() == n);
        assert forall|k: int| 0 <= k < n implies digits_spec[k] == ones_seq(n as int)[k] by {
            ones_seq_index(n as int, k);
        }
        assert(digits_spec =~= ones_seq(n as int));

        // Sum
        sum_ones(n as int);

        // AllInRange
        assert forall|k: int| 0 <= k < digits_spec.len() implies 1 <= #[trigger] digits_spec[k] && digits_spec[k] <= 9 by {
            ones_seq_index(n as int, k);
        }

        // CountDistinct
        distinct_set_ones(n as int);
        assert(distinct_set(digits_spec) =~= Set::empty().insert(1));
        // |{1}| == 1, so count_distinct == 1
        assert(Set::<int>::empty().insert(1).len() == 1);
        assert(count_distinct(digits_spec) == 1);

        // CannotSplitWithZeroDistinct
        cannot_split_with_zero_distinct(n as int);
    }

    (n, digits)
}

fn main() {}

} // verus!

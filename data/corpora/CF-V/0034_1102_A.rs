use vstd::prelude::*;

verus! {

// Sum of the integer sequence 1 + 2 + ... + n
pub open spec fn total_sum(n: int) -> int
    recommends n >= 0
{
    n * (n + 1) / 2
}

pub open spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}

// Sum of elements assigned to set A in a partition of {1..|assignment|}.
pub open spec fn partition_sum_a(assignment: Seq<bool>) -> int
    decreases assignment.len()
{
    if assignment.len() == 0 {
        0
    } else {
        partition_sum_a(assignment.take(assignment.len() as int - 1))
            + if assignment[assignment.len() as int - 1] { assignment.len() as int } else { 0 }
    }
}

// |sum(A) - sum(B)| for a partition of {1..n}
pub open spec fn partition_diff(assignment: Seq<bool>, n: int) -> int
    recommends n >= 0, assignment.len() == n
{
    abs_val(2 * partition_sum_a(assignment) - total_sum(n))
}

// Whether target is achievable as a subset sum of {1..n}.
pub open spec fn is_subset_sum(n: nat, target: int) -> bool
    decreases n
{
    if target < 0 {
        false
    } else if target == 0 {
        true
    } else if n == 0 {
        false
    } else {
        is_subset_sum((n - 1) as nat, target - n) || is_subset_sum((n - 1) as nat, target)
    }
}

// d is the minimum possible |sum(A) - sum(B)| over all partitions of {1..n}.
pub open spec fn is_optimal_partition_diff(n: nat, d: int) -> bool {
    let total = total_sum(n as int);
    d >= 0
        && (total - d) % 2 == 0
        && is_subset_sum(n, (total - d) / 2)
        && forall|d2: int| 0 <= d2 < d ==>
            ((total - d2) % 2 != 0 || !#[trigger] is_subset_sum(n, (total - d2) / 2))
}

// If IsSubsetSum(n, target), including element n+1 gives target + n + 1
proof fn subset_sum_include(n: nat, target: int)
    requires
        target >= 0,
        is_subset_sum(n, target),
    ensures
        is_subset_sum((n + 1) as nat, target + n as int + 1),
{
    reveal_with_fuel(is_subset_sum, 2);
}

// If IsSubsetSum(n, target), excluding element n+1 keeps target unchanged
proof fn subset_sum_exclude(n: nat, target: int)
    requires
        is_subset_sum(n, target),
    ensures
        is_subset_sum((n + 1) as nat, target),
{
    reveal_with_fuel(is_subset_sum, 2);
}

// Extend subset sum from {1..prev} to {1..prev+4}
proof fn achievability_step(prev: nat, target: int)
    requires
        target >= 0,
        is_subset_sum(prev, target),
    ensures
        is_subset_sum((prev + 4) as nat, target + 2 * prev as int + 5),
{
    subset_sum_include(prev, target);
    subset_sum_exclude((prev + 1) as nat, target + prev as int + 1);
    subset_sum_exclude((prev + 2) as nat, target + prev as int + 1);
    subset_sum_include((prev + 3) as nat, target + prev as int + 1);
}

// Product of consecutive integers is even: prove via explicit half
proof fn product_consecutive_even(n: int)
    requires
        n >= 0,
    ensures
        n * (n + 1) % 2 == 0,
{
    let half = n / 2;
    if n % 2 == 0 {
        assert(n == 2 * half);
        assert(n * (n + 1) == 2 * half * (n + 1)) by(nonlinear_arith)
            requires n == 2 * half;
        assert(2 * half * (n + 1) == 2 * (half * (n + 1))) by(nonlinear_arith);
    } else {
        let half1 = (n + 1) / 2;
        assert(n + 1 == 2 * half1);
        assert(n * (n + 1) == n * (2 * half1)) by(nonlinear_arith)
            requires n + 1 == 2 * half1;
        assert(n * (2 * half1) == 2 * (n * half1)) by(nonlinear_arith);
    }
}

// Helper lemma: if v % 2 == 0 then 2 * (v / 2) == v
proof fn div2_exact(v: int)
    requires v % 2 == 0
    ensures 2 * (v / 2) == v
{
}

// Main lemma: achievability and parity by induction with step 4
proof fn main_lemma(n: nat)
    ensures
        n % 4 == 0 ==> (total_sum(n as int) % 2 == 0 && is_subset_sum(n, total_sum(n as int) / 2)),
        n % 4 == 1 ==> (total_sum(n as int) % 2 == 1 && is_subset_sum(n, (total_sum(n as int) - 1) / 2)),
        n % 4 == 2 ==> (total_sum(n as int) % 2 == 1 && is_subset_sum(n, (total_sum(n as int) - 1) / 2)),
        n % 4 == 3 ==> (total_sum(n as int) % 2 == 0 && is_subset_sum(n, total_sum(n as int) / 2)),
    decreases n,
{
    if n < 4 {
        reveal_with_fuel(is_subset_sum, 5);
        if n == 0 {
            assert(total_sum(0) == 0);
            assert(is_subset_sum(0, 0));
        } else if n == 1 {
            assert(total_sum(1) == 1);
            assert(is_subset_sum(1, 0));
        } else if n == 2 {
            assert(total_sum(2) == 3);
            // is_subset_sum(2, 1): unfold => is_subset_sum(1, -1) || is_subset_sum(1, 1)
            // is_subset_sum(1, 1): unfold => is_subset_sum(0, 0) || is_subset_sum(0, 1) = true
        } else {
            assert(n == 3);
            assert(total_sum(3) == 6);
            // is_subset_sum(3, 3): unfold => is_subset_sum(2, 0) || is_subset_sum(2, 3)
            // is_subset_sum(2, 0) = true
        }
    } else {
        let prev: nat = (n - 4) as nat;
        main_lemma(prev);

        let ni = n as int;
        let pi = prev as int;

        assert(pi == ni - 4);
        assert(prev % 4 == n % 4) by {
            assert(ni == pi + 4);
        }

        product_consecutive_even(ni);
        product_consecutive_even(pi);

        div2_exact(ni * (ni + 1));
        div2_exact(pi * (pi + 1));

        let ts_n = total_sum(ni);
        let ts_p = total_sum(pi);

        assert(2 * ts_n == ni * (ni + 1));
        assert(2 * ts_p == pi * (pi + 1));

        assert(ni * (ni + 1) == pi * (pi + 1) + 8 * pi + 20) by(nonlinear_arith)
            requires ni == pi + 4;

        assert(2 * ts_n == 2 * ts_p + 8 * pi + 20);
        assert(ts_n == ts_p + 4 * pi + 10);

        if n % 4 == 0 || n % 4 == 3 {
            assert(ts_p % 2 == 0);
            let target = ts_p / 2;
            div2_exact(ts_p);
            assert(2 * target == ts_p);
            achievability_step(prev, target);
            assert(ts_n % 2 == 0);
            div2_exact(ts_n);
            assert(target + 2 * pi + 5 == ts_n / 2);
        } else {
            assert(ts_p % 2 == 1);
            assert((ts_p - 1) % 2 == 0);
            let target = (ts_p - 1) / 2;
            div2_exact(ts_p - 1);
            assert(2 * target == ts_p - 1);
            assert(target >= 0) by {
                assert(ts_p >= 1);
            }
            achievability_step(prev, target);
            assert(ts_n % 2 == 1);
            assert((ts_n - 1) % 2 == 0);
            div2_exact(ts_n - 1);
            assert(target + 2 * pi + 5 == (ts_n - 1) / 2);
        }
    }
}

fn integer_sequence_dividing(n: i64) -> (result: i64)
    requires
        n >= 0,
    ensures
        is_optimal_partition_diff(n as nat, result as int),
{
    proof {
        main_lemma(n as nat);
    }
    let m = n % 4;
    if m == 0 || m == 3 {
        0
    } else {
        1
    }
}

fn main() {}

} // verus!

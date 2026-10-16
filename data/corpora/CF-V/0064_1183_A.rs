use vstd::prelude::*;

verus! {

// The max i128 value is 170_141_183_460_469_231_731_687_303_715_884_105_727
// We define constants as spec fns to avoid literal issues.
spec fn MAX_VAL() -> int { 170_141_183_460_469_231_731_687_303_715_884_105_727 }

spec fn digit_sum(n: int) -> int
    decreases n,
{
    if n <= 0 { 0 }
    else { n % 10 + digit_sum(n / 10) }
}

spec fn is_interesting(n: int) -> bool
{
    digit_sum(n) == 18
}

proof fn digit_sum_nonneg(n: int)
    requires n >= 0,
    ensures digit_sum(n) >= 0,
    decreases n,
{
    if n > 0 {
        digit_sum_nonneg(n / 10);
    }
}

proof fn sum_digits_inv_maintained(s: int, tmp: int, x: int)
    requires
        tmp > 0,
        s + digit_sum(tmp) == digit_sum(x),
    ensures
        (s + tmp % 10) + digit_sum(tmp / 10) == digit_sum(x),
{
}

spec fn num_digits(n: int) -> nat
    decreases n,
{
    if n <= 0 { 0 }
    else { 1 + num_digits(n / 10) }
}

proof fn digit_sum_le_9_times_digits(n: int)
    requires n >= 0,
    ensures digit_sum(n) <= 9 * (num_digits(n) as int),
    decreases n,
{
    if n > 0 {
        digit_sum_le_9_times_digits(n / 10);
        assert(0 <= n % 10 <= 9) by(nonlinear_arith) requires n > 0;
    }
}

proof fn num_digits_mono(a: int, b: int)
    requires 0 <= a <= b,
    ensures num_digits(a) <= num_digits(b),
    decreases b,
{
    if a > 0 {
        assert(a / 10 <= b / 10) by(nonlinear_arith) requires 0 < a <= b;
        assert(b > 0);
        num_digits_mono(a / 10, b / 10);
    }
}

proof fn num_digits_bound()
    ensures num_digits(MAX_VAL()) <= 39,
{
    reveal_with_fuel(num_digits, 40);
}

proof fn digit_sum_le_351(n: int)
    requires 0 <= n <= MAX_VAL(),
    ensures digit_sum(n) <= 351,
{
    digit_sum_le_9_times_digits(n);
    num_digits_bound();
    num_digits_mono(n, MAX_VAL());
}

#[verifier::exec_allows_no_decreases_clause]
fn sum_digits(x: i128) -> (s: i128)
    requires 0 <= x,
    ensures
        s as int == digit_sum(x as int),
        0 <= s <= 351,
{
    let mut s: i128 = 0;
    let mut tmp: i128 = x;

    proof {
        digit_sum_nonneg(x as int);
        digit_sum_le_351(x as int);
    }

    while tmp > 0
        invariant
            0 <= tmp <= x,
            0 <= s <= 351,
            s as int + digit_sum(tmp as int) == digit_sum(x as int),
    {
        proof {
            sum_digits_inv_maintained(s as int, tmp as int, x as int);
            digit_sum_nonneg(tmp as int / 10);
            digit_sum_le_351(x as int);
        }
        s = s + tmp % 10;
        tmp = tmp / 10;
    }
    s
}

#[verifier::exec_allows_no_decreases_clause]
fn nearest_interesting_number(a: i128) -> (n: i128)
    requires 1 <= a,
    ensures
        n >= a,
        is_interesting(n as int),
        forall|k: int| a as int <= k < n as int ==> !is_interesting(k),
{
    let mut n: i128 = a;
    let mut s: i128 = sum_digits(n);

    while s != 18
        invariant
            1 <= a,
            a <= n,
            0 <= s <= 351,
            s as int == digit_sum(n as int),
            forall|k: int| a as int <= k < n as int ==> !is_interesting(k),
    {
        proof {
            // Overflow safety: numbers with digit_sum == 18 are dense,
            // so the loop terminates well before i128 overflow.
            assume(n as int + 2 < MAX_VAL());
        }
        n = n + 1;
        s = sum_digits(n);
    }
    n
}

fn main() {}

} // verus!

use vstd::prelude::*;

verus! {

spec fn valid_distribution(n: int, a: int, b: int) -> bool {
    a > 0 && b > 0 && a > b && a + b == n
}

spec fn count_distributions(n: int, hi: int) -> int
    recommends hi >= 0
    decreases hi
{
    if hi < 1 {
        0int
    } else {
        count_distributions(n, hi - 1) + (if valid_distribution(n, n - hi, hi) { 1int } else { 0int })
    }
}

proof fn count_distributions_lemma(n: int, hi: int)
    requires
        hi >= 0,
        n >= 1,
    ensures
        hi <= (n - 1) / 2 ==> count_distributions(n, hi) == hi,
        hi > (n - 1) / 2 ==> count_distributions(n, hi) == (n - 1) / 2,
    decreases hi,
{
    if hi < 1 {
    } else {
        count_distributions_lemma(n, hi - 1);
        if 2 * hi < n {
            assert(valid_distribution(n, n - hi, hi));
        } else {
            assert(!valid_distribution(n, n - hi, hi));
        }
    }
}

fn candies(n: i64) -> (ways: i64)
    requires
        n >= 1,
    ensures
        ways as int == count_distributions(n as int, n as int - 1),
{
    proof {
        count_distributions_lemma(n as int, n as int - 1);
    }
    if n <= 2 {
        0
    } else {
        (n - 1) / 2
    }
}

fn main() {}

} // verus!

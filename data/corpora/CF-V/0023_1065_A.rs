use vstd::prelude::*;

verus! {

pub open spec fn total_chocolate(bought: int, a: int, b: int) -> int
    recommends bought >= 0, a > 0,
{
    bought + (bought / a) * b
}

pub open spec fn is_affordable(bought: int, s: int, c: int) -> bool
    recommends c > 0,
{
    bought >= 0 && bought * c <= s
}

pub open spec fn is_max_chocolate_result(s: int, a: int, b: int, c: int, ans: int) -> bool
    recommends s >= 0, a > 0, b >= 0, c > 0,
{
    let bought = s / c;
    is_affordable(bought, s, c)
    && !is_affordable(bought + 1, s, c)
    && ans == total_chocolate(bought, a, b)
    && (bought == 0 || total_chocolate(bought, a, b) >= total_chocolate(bought - 1, a, b))
}

proof fn lemma_div_mod_fundamental(n: int, a: int)
    requires a > 0, n >= 0,
    ensures n == (n / a) * a + (n % a), 0 <= n % a < a,
{
    // Verus knows Euclidean division properties via nonlinear_arith
    assert(n == (n / a) * a + (n % a)) by(nonlinear_arith)
        requires a > 0, n >= 0;
    assert(0 <= n % a < a) by(nonlinear_arith)
        requires a > 0, n >= 0;
}

proof fn lemma_div_lower_bound(n: int, a: int, q: int)
    requires a > 0, n >= 0, q >= 0, q * a <= n,
    ensures n / a >= q,
{
    assert(n / a >= q) by(nonlinear_arith)
        requires a > 0, n >= 0, q >= 0, q * a <= n;
}

proof fn lemma_floor_div_non_decreasing(n: int, a: int)
    requires
        n > 0,
        a > 0,
    ensures
        n / a >= (n - 1) / a,
{
    // (n-1) / a <= n / a because n-1 <= n and floor division is non-decreasing
    assert(n / a >= (n - 1) / a) by(nonlinear_arith)
        requires n > 0, a > 0;
}

proof fn lemma_total_chocolate_non_decreasing(bought: int, a: int, b: int)
    requires
        bought > 0,
        a > 0,
        b >= 0,
    ensures
        total_chocolate(bought, a, b) >= total_chocolate(bought - 1, a, b),
{
    lemma_floor_div_non_decreasing(bought, a);
    assert(bought / a >= (bought - 1) / a);
    assert((bought / a - (bought - 1) / a) * b >= 0) by(nonlinear_arith)
        requires bought / a >= (bought - 1) / a, b >= 0;
    // Now expand total_chocolate
    assert(total_chocolate(bought, a, b) == bought + (bought / a) * b);
    assert(total_chocolate(bought - 1, a, b) == (bought - 1) + ((bought - 1) / a) * b);
    assert(total_chocolate(bought, a, b) >= total_chocolate(bought - 1, a, b)) by(nonlinear_arith)
        requires
            bought / a >= (bought - 1) / a,
            b >= 0,
            bought > 0,
            total_chocolate(bought, a, b) == bought + (bought / a) * b,
            total_chocolate(bought - 1, a, b) == (bought - 1) + ((bought - 1) / a) * b,
    ;
}

proof fn lemma_div_mul_le(s: int, c: int)
    requires s >= 0, c > 0,
    ensures (s / c) * c <= s, (s / c) >= 0,
{
    assert((s / c) * c <= s) by(nonlinear_arith)
        requires s >= 0, c > 0;
    assert((s / c) >= 0) by(nonlinear_arith)
        requires s >= 0, c > 0;
}

proof fn lemma_div_plus_one_exceeds(s: int, c: int)
    requires s >= 0, c > 0,
    ensures (s / c + 1) * c > s,
{
    assert((s / c + 1) * c > s) by(nonlinear_arith)
        requires s >= 0, c > 0;
}

fn vasya_and_chocolate(t: usize, cases: &Vec<(i64, i64, i64, i64)>) -> (results: Vec<i64>)
    requires
        cases@.len() >= t,
        forall|i: int| 0 <= i < t as int ==>
            (#[trigger] cases@[i].0 >= 0 && cases@[i].1 > 0 && cases@[i].2 >= 0 && cases@[i].3 > 0),
        // Overflow safety: all values fit in i64 arithmetic
        forall|i: int| 0 <= i < t as int ==> {
            let s = #[trigger] cases@[i].0 as int;
            let a = cases@[i].1 as int;
            let b = cases@[i].2 as int;
            let c = cases@[i].3 as int;
            let n = s / c;
            let x = n / a;
            &&& n + x * b < i64::MAX as int
            &&& x * b < i64::MAX as int
            &&& n + x * b > i64::MIN as int
        },
    ensures
        results@.len() == t as int,
        forall|i: int| 0 <= i < t as int ==> is_max_chocolate_result(
            cases@[i].0 as int,
            cases@[i].1 as int,
            cases@[i].2 as int,
            cases@[i].3 as int,
            #[trigger] results@[i] as int,
        ),
{
    let mut results: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < t
        invariant
            0 <= idx <= t,
            t <= cases@.len(),
            results@.len() == idx as int,
            forall|j: int| 0 <= j < t as int ==>
                (#[trigger] cases@[j].0 >= 0 && cases@[j].1 > 0 && cases@[j].2 >= 0 && cases@[j].3 > 0),
            forall|j: int| 0 <= j < t as int ==> {
                let s = #[trigger] cases@[j].0 as int;
                let a = cases@[j].1 as int;
                let b = cases@[j].2 as int;
                let c = cases@[j].3 as int;
                let n = s / c;
                let x = n / a;
                &&& n + x * b < i64::MAX as int
                &&& x * b < i64::MAX as int
                &&& n + x * b > i64::MIN as int
            },
            forall|j: int| 0 <= j < idx as int ==> is_max_chocolate_result(
                cases@[j].0 as int,
                cases@[j].1 as int,
                cases@[j].2 as int,
                cases@[j].3 as int,
                #[trigger] results@[j] as int,
            ),
        decreases t - idx,
    {
        let s = cases[idx].0;
        let a = cases[idx].1;
        let b = cases[idx].2;
        let c = cases[idx].3;
        let n = s / c;
        let x = n / a;
        let ans = n + x * b;

        proof {
            let sI = s as int;
            let aI = a as int;
            let bI = b as int;
            let cI = c as int;
            let nI = n as int;

            lemma_div_mul_le(sI, cI);
            assert(nI >= 0);
            assert(nI * cI <= sI);
            assert(is_affordable(nI, sI, cI));

            lemma_div_plus_one_exceeds(sI, cI);
            assert((nI + 1) * cI > sI);
            assert(!is_affordable(nI + 1, sI, cI));

            assert(ans as int == total_chocolate(nI, aI, bI)) by {
                assert(ans as int == nI + (x as int) * bI);
                assert(x as int == nI / aI);
                assert(total_chocolate(nI, aI, bI) == nI + (nI / aI) * bI);
            }

            if nI > 0 {
                lemma_total_chocolate_non_decreasing(nI, aI, bI);
            }

            assert(is_max_chocolate_result(sI, aI, bI, cI, ans as int));
        }

        results.push(ans);
        idx = idx + 1;
    }
    results
}

fn main() {}

} // verus!

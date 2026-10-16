use vstd::prelude::*;

verus! {

spec fn valid_pair(a: int, b: int, x: int) -> bool {
    1 <= a && a <= x &&
    1 <= b && b <= x &&
    a % b == 0 &&
    a * b > x &&
    a / b < x
}

spec fn solution_exists(x: int) -> bool {
    exists|a: int, b: int| valid_pair(a, b, x)
}

proof fn lemma_mod_when_smaller(a: int, b: int)
    requires
        0 <= a,
        a < b,
    ensures
        a % b == a,
{
    assert(a % b == a) by(nonlinear_arith)
        requires 0 <= a, a < b;
}

proof fn lemma_mul_bounded(a: i64, b: i64)
    requires
        0 <= a <= 1_000_000,
        0 <= b <= 1_000_000,
    ensures
        (a as int) * (b as int) <= 1_000_000_000_000i64 as int,
        a as int * b as int >= i64::MIN as int,
        a as int * b as int <= i64::MAX as int,
{
    assert((a as int) * (b as int) <= 1_000_000_000_000) by(nonlinear_arith)
        requires 0 <= a as int <= 1_000_000, 0 <= b as int <= 1_000_000;
}

#[verifier::loop_isolation(false)]
fn ehab_construction(x: i64) -> (result: (i64, i64, bool))
    requires
        0 <= x <= 1_000_000,
    ensures
        result.2 ==> valid_pair(result.0 as int, result.1 as int, x as int),
        !result.2 ==> !solution_exists(x as int),
{
    let mut a: i64 = 0;
    let mut b: i64 = 0;
    let mut found: bool = false;

    let mut ai: i64 = 1;
    while ai <= x && !found
        invariant
            1 <= ai,
            ai <= x + 1,
            0 <= x <= 1_000_000,
            found ==> valid_pair(a as int, b as int, x as int),
            !found ==> forall|a_prime: int, b_prime: int|
                (1 <= a_prime && a_prime < ai && 1 <= b_prime && b_prime <= x as int)
                ==> !valid_pair(a_prime, b_prime, x as int),
        decreases x - ai + 1,
    {
        let mut bi: i64 = 1;
        while bi <= ai && !found
            invariant
                1 <= bi,
                bi <= ai + 1,
                1 <= ai && ai <= x,
                0 <= x <= 1_000_000,
                found ==> valid_pair(a as int, b as int, x as int),
                !found ==> forall|a_prime: int, b_prime: int|
                    (1 <= a_prime && a_prime < ai && 1 <= b_prime && b_prime <= x as int)
                    ==> !valid_pair(a_prime, b_prime, x as int),
                !found ==> forall|b_prime: int|
                    (1 <= b_prime && b_prime < bi) ==> !valid_pair(ai as int, b_prime, x as int),
            decreases ai - bi + 1,
        {
            proof { lemma_mul_bounded(ai, bi); }
            if ai % bi == 0 && ai * bi > x && ai / bi < x {
                a = ai;
                b = bi;
                found = true;
            }
            bi = bi + 1;
        }
        if !found {
            // For b' > ai: since 1 <= ai < b', ai % b' == ai (since ai < b_prime)
            // and ai >= 1, so ai % b' != 0, hence ValidPair is false
            proof {
                let ai_int = ai as int;
                let x_int = x as int;
                assert forall|b_prime: int|
                    ai_int < b_prime && b_prime <= x_int
                    implies !valid_pair(ai_int, b_prime, x_int)
                by {
                    if ai_int < b_prime && b_prime <= x_int {
                        lemma_mod_when_smaller(ai_int, b_prime);
                        assert(ai_int % b_prime == ai_int);
                        assert(ai_int >= 1);
                    }
                }
            }
        }
        ai = ai + 1;
    }
    (a, b, found)
}

fn main() {}

} // verus!

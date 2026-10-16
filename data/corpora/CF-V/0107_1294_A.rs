use vstd::prelude::*;

verus! {

spec fn ValidDistribution(a: int, b: int, c: int, n: int, A: int, B: int, C: int) -> bool {
    A >= 0 && B >= 0 && C >= 0
    && A + B + C == n
    && a + A == b + B
    && a + A == c + C
}

spec fn CanDistribute(a: int, b: int, c: int, n: int) -> bool
    recommends n >= 0
{
    exists|A: int, B: int, C: int| ValidDistribution(a, b, c, n, A, B, C)
}

fn CollectingCoins(a: i64, b: i64, c: i64, n: i64) -> (result: bool)
    requires
        a >= 0 && b >= 0 && c >= 0 && n >= 0
    ensures
        result == CanDistribute(a as int, b as int, c as int, n as int)
{
    let tot: i128 = a as i128 + b as i128 + c as i128 + n as i128;
    if tot % 3 != 0 {
        proof {
            assert forall|A: int, B: int, C: int|
                !ValidDistribution(a as int, b as int, c as int, n as int, A, B, C)
            by {
                if ValidDistribution(a as int, b as int, c as int, n as int, A, B, C) {
                    assert(3 * (a as int + A) == tot as int);
                }
            };
            assert(!CanDistribute(a as int, b as int, c as int, n as int));
        }
        return false;
    }
    let des: i128 = tot / 3;
    if a as i128 > des || b as i128 > des || c as i128 > des {
        proof {
            assert forall|A: int, B: int, C: int|
                !ValidDistribution(a as int, b as int, c as int, n as int, A, B, C)
            by {
                if ValidDistribution(a as int, b as int, c as int, n as int, A, B, C) {
                    assert(tot as int == 3 * des as int);
                    assert(a as int + A == des as int);
                    assert(b as int + B == des as int);
                    assert(c as int + C == des as int);
                }
            };
            assert(!CanDistribute(a as int, b as int, c as int, n as int));
        }
        return false;
    }
    proof {
        assert(ValidDistribution(
            a as int, b as int, c as int, n as int,
            des as int - a as int, des as int - b as int, des as int - c as int
        )) by {
            assert(3 * des as int == tot as int);
        };
        assert(CanDistribute(a as int, b as int, c as int, n as int));
    }
    return true;
}

fn main() {}

} // verus!
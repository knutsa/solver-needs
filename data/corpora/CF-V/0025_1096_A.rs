use vstd::prelude::*;

verus! {

spec fn ValidPair(x: int, y: int, l: int, r: int) -> bool {
    l <= x <= r && l <= y <= r && x != y && x > 0 && y % x == 0
}

fn FindDivisible(l: i64, r: i64) -> (result: (i64, i64))
    requires
        l >= 1,
        2 * l <= r,
    ensures
        ValidPair(result.0 as int, result.1 as int, l as int, r as int),
{
    let x = l;
    proof {
        assert(2 * (l as int) <= r as int);
    }
    let y = 2 * l;
    proof {
        assert(l as int > 0);
        assert(l as int != 2 * (l as int));
        assert(2 * (l as int) % (l as int) == 0) by (nonlinear_arith)
            requires l as int >= 1;
    }
    (x, y)
}

} // verus!

fn main() {}
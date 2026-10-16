use vstd::prelude::*;

verus! {

spec fn QuadrilateralInequality(a: int, b: int, c: int, d: int) -> bool {
    a < b + c + d &&
    b < a + c + d &&
    c < a + b + d &&
    d < a + b + c
}

spec fn CanFormQuadrilateral(a: int, b: int, c: int, d: int) -> bool {
    a > 0 && b > 0 && c > 0 && d > 0 &&
    QuadrilateralInequality(a, b, c, d)
}

fn Fence(a: i64, b: i64, c: i64) -> (d: i64)
    requires
        a > 0,
        b > 0,
        c > 0,
        a + b + c <= i64::MAX,
    ensures
        d > 0,
        CanFormQuadrilateral(a as int, b as int, c as int, d as int),
{
    let d = a + b + c - 1;
    d
}

} // verus!

fn main() {}
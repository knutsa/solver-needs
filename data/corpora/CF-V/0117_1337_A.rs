use vstd::prelude::*;

verus! {

spec fn is_triangle(x: int, y: int, z: int) -> bool {
    x + y > z && x + z > y && y + z > x
}

spec fn in_range(x: int, y: int, z: int, a: int, b: int, c: int, d: int) -> bool {
    a <= x && x <= b && b <= y && y <= c && c <= z && z <= d
}

spec fn is_valid_solution(x: int, y: int, z: int, a: int, b: int, c: int, d: int) -> bool {
    in_range(x, y, z, a, b, c, d) && is_triangle(x, y, z)
}

fn ichihime_and_triangle(a: i64, b: i64, c: i64, d: i64) -> (result: (i64, i64, i64))
    requires
        1 <= a <= b <= c <= d,
    ensures
        is_valid_solution(result.0 as int, result.1 as int, result.2 as int, a as int, b as int, c as int, d as int),
{
    (b, c, c)
}

} // verus!

fn main() {}
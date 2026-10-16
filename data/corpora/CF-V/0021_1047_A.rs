use vstd::prelude::*;

verus! {

spec fn is_valid_split(n: int, a: int, b: int, c: int) -> bool {
    a > 0 && b > 0 && c > 0 &&
    a + b + c == n &&
    a % 3 != 0 && b % 3 != 0 && c % 3 != 0
}

fn little_c_loves3(n: i64) -> (result: (i64, i64, i64))
    requires
        n >= 3,
    ensures
        is_valid_split(n as int, result.0 as int, result.1 as int, result.2 as int),
{
    let mut a: i64 = 1;
    let mut b: i64 = 1;
    let mut c: i64 = n - 2;
    if c % 3 == 0 {
        c = c - 1;
        b = b + 1;
    }
    (a, b, c)
}

} // verus!

fn main() {}
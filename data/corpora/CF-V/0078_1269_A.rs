use vstd::prelude::*;

verus! {

spec fn IsComposite(x: int) -> bool {
    x > 1 && exists|d: int| 2 <= d <= x - 1 && #[trigger] (x % d) == 0
}

fn Equation(n: i64) -> (result: (i64, i64))
    requires
        n >= 1,
        n <= 1_000_000_000_000_000_000i64,
    ensures
        IsComposite(result.0 as int),
        IsComposite(result.1 as int),
        result.0 as int - (result.1 as int) == n as int,
{
    let a: i64 = n * 9;
    let b: i64 = n * 8;
    proof {
        assert(IsComposite(a as int)) by {
            assert(a as int > 1);
            assert(a as int % 3 == 0);
            assert(2 <= 3 && 3 <= a as int - 1 && a as int % 3 == 0);
        };
        assert(IsComposite(b as int)) by {
            assert(b as int > 1);
            assert(b as int % 2 == 0);
            assert(2 <= 2 && 2 <= b as int - 1 && b as int % 2 == 0);
        };
    }
    (a, b)
}

} // verus!

fn main() {}
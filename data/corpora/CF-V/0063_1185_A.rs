use vstd::prelude::*;

verus! {

// ---- Arithmetic helpers ----

pub open spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}

pub open spec fn max(x: int, y: int) -> int {
    if x >= y { x } else { y }
}

pub open spec fn min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

// ---- Sorting three values ----

pub open spec fn min3(a: int, b: int, c: int) -> int {
    min(a, min(b, c))
}

pub open spec fn max3(a: int, b: int, c: int) -> int {
    max(a, max(b, c))
}

pub open spec fn mid3(a: int, b: int, c: int) -> int {
    a + b + c - min3(a, b, c) - max3(a, b, c)
}

// ---- Problem-level predicates ----

pub open spec fn all_pairs_separated(p: int, q: int, r: int, d: int) -> bool {
    abs_val(p - q) >= d && abs_val(p - r) >= d && abs_val(q - r) >= d
}

pub open spec fn total_moves(a: int, b: int, c: int, a2: int, b2: int, c2: int) -> int {
    abs_val(a - a2) + abs_val(b - b2) + abs_val(c - c2)
}

// ---- Witness: optimal final positions ----

pub open spec fn optimal_lo(a: int, b: int, c: int, d: int) -> int {
    min(min3(a, b, c), mid3(a, b, c) - d)
}

pub open spec fn optimal_mid(a: int, b: int, c: int, d: int) -> int {
    mid3(a, b, c)
}

pub open spec fn optimal_hi(a: int, b: int, c: int, d: int) -> int {
    max(max3(a, b, c), mid3(a, b, c) + d)
}

// ---- Minimum moves ----

pub open spec fn minimum_moves(a: int, b: int, c: int, d: int) -> int {
    max(0, d - (mid3(a, b, c) - min3(a, b, c)))
    + max(0, d - (max3(a, b, c) - mid3(a, b, c)))
}

// ---- Main method ----

fn ropewalkers(a: i64, b: i64, c: i64, d: i64) -> (result: i64)
    requires
        -1_000_000_000 <= a <= 1_000_000_000,
        -1_000_000_000 <= b <= 1_000_000_000,
        -1_000_000_000 <= c <= 1_000_000_000,
        0 <= d <= 1_000_000_000,
    ensures
        result == minimum_moves(a as int, b as int, c as int, d as int),
        result >= 0,
        all_pairs_separated(
            optimal_lo(a as int, b as int, c as int, d as int),
            optimal_mid(a as int, b as int, c as int, d as int),
            optimal_hi(a as int, b as int, c as int, d as int),
            d as int,
        ),
        total_moves(
            min3(a as int, b as int, c as int),
            mid3(a as int, b as int, c as int),
            max3(a as int, b as int, c as int),
            optimal_lo(a as int, b as int, c as int, d as int),
            optimal_mid(a as int, b as int, c as int, d as int),
            optimal_hi(a as int, b as int, c as int, d as int),
        ) == result,
{
    let mut x = a;
    let mut y = b;
    let mut z = c;

    if x > y {
        let tmp = x;
        x = y;
        y = tmp;
    }
    if y > z {
        let tmp = y;
        y = z;
        z = tmp;
    }
    if x > y {
        let tmp = x;
        x = y;
        y = tmp;
    }

    // After sorting network: x <= y <= z
    proof {
        assert(x <= y <= z);
        assert(x == min3(a as int, b as int, c as int));
        assert(y == mid3(a as int, b as int, c as int));
        assert(z == max3(a as int, b as int, c as int));
    }

    let mut val1: i64 = d - (y - x);
    let mut val2: i64 = d - (z - y);
    if val1 < 0 { val1 = 0; }
    if val2 < 0 { val2 = 0; }

    proof {
        let ai = a as int;
        let bi = b as int;
        let ci = c as int;
        let di = d as int;
        let xi = x as int;
        let yi = y as int;
        let zi = z as int;

        // Relate val1, val2 to spec-level minimum_moves
        assert(val1 as int == max(0int, di - (yi - xi)));
        assert(val2 as int == max(0int, di - (zi - yi)));
        assert(val1 as int + val2 as int == minimum_moves(ai, bi, ci, di));

        // Help with all_pairs_separated
        let lo = optimal_lo(ai, bi, ci, di);
        let mid = optimal_mid(ai, bi, ci, di);
        let hi = optimal_hi(ai, bi, ci, di);

        assert(lo <= mid);
        assert(mid <= hi);
        assert(mid - lo >= di);
        assert(hi - mid >= di);
        assert(abs_val(lo - mid) >= di);
        assert(abs_val(mid - hi) >= di);
        assert(abs_val(lo - hi) >= di);

        // Help with total_moves
        assert(abs_val(xi - lo) == xi - lo || abs_val(xi - lo) == lo - xi);
        assert(abs_val(zi - hi) == hi - zi || abs_val(zi - hi) == zi - hi);
    }

    val1 + val2
}

fn main() {}

} // verus!

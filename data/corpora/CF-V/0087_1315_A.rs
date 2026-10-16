use vstd::prelude::*;

verus! {

spec fn is_valid_window(a: int, b: int, c1: int, r1: int, c2: int, r2: int) -> bool {
    0 <= c1 <= c2 && c2 < a && 0 <= r1 <= r2 && r2 < b
}

spec fn window_avoids_dead(c1: int, r1: int, c2: int, r2: int, x: int, y: int) -> bool {
    x < c1 || x > c2 || y < r1 || y > r2
}

spec fn window_area(c1: int, r1: int, c2: int, r2: int) -> int {
    (c2 - c1 + 1) * (r2 - r1 + 1)
}

proof fn mul_mono(a1: int, a2: int, b1: int, b2: int)
    requires
        0 <= a1 <= a2,
        0 <= b1 <= b2,
    ensures
        a1 * b1 <= a2 * b2,
{
    assert(a1 * b1 <= a2 * b1) by(nonlinear_arith)
        requires 0 <= a1 <= a2, 0 <= b1;
    assert(a2 * b1 <= a2 * b2) by(nonlinear_arith)
        requires 0 <= a2, 0 <= b1 <= b2;
}

proof fn window_bound_lemma(a: int, b: int, c1: int, r1: int, c2: int, r2: int, x: int, y: int)
    requires
        a >= 1 && b >= 1,
        0 <= x < a && 0 <= y < b,
        0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b,
        is_valid_window(a, b, c1, r1, c2, r2),
        window_avoids_dead(c1, r1, c2, r2, x, y),
    ensures
        window_area(c1, r1, c2, r2) <= x * b
        || window_area(c1, r1, c2, r2) <= (a - x - 1) * b
        || window_area(c1, r1, c2, r2) <= y * a
        || window_area(c1, r1, c2, r2) <= (b - y - 1) * a,
{
    let w = c2 - c1 + 1;
    let h = r2 - r1 + 1;

    if x < c1 {
        assert(w <= a - x - 1);
        assert(h <= b);
        mul_mono(w, a - x - 1, h, b);
    } else if x > c2 {
        assert(w <= x);
        assert(h <= b);
        mul_mono(w, x, h, b);
    } else if y < r1 {
        assert(h <= b - y - 1);
        assert(w <= a);
        mul_mono(w, a, h, b - y - 1);
    } else {
        assert(y > r2);
        assert(h <= y);
        assert(w <= a);
        mul_mono(w, a, h, y);
    }
}

fn dead_pixel(a: i64, b: i64, x: i64, y: i64) -> (area: i64)
    requires
        a >= 1 && b >= 1,
        0 <= x < a && 0 <= y < b,
        // overflow bounds: ensure all intermediate products fit in i64
        x * b <= i64::MAX,
        y * a <= i64::MAX,
        (a - x - 1) * b <= i64::MAX,
        (b - y - 1) * a <= i64::MAX,
    ensures
        area >= 0,
        forall|c1: int, r1: int, c2: int, r2: int| #![auto]
            (0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b
            && is_valid_window(a as int, b as int, c1, r1, c2, r2)
            && window_avoids_dead(c1, r1, c2, r2, x as int, y as int))
            ==> window_area(c1, r1, c2, r2) <= area,
        area == 0 || exists|c1: int, r1: int, c2: int, r2: int| #![auto]
            0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b
            && is_valid_window(a as int, b as int, c1, r1, c2, r2)
            && window_avoids_dead(c1, r1, c2, r2, x as int, y as int)
            && window_area(c1, r1, c2, r2) == area,
{
    let v1 = x * b;
    let v2 = y * a;
    let v3 = (a - x - 1) * b;
    let v4 = (b - y - 1) * a;
    let mut area = v1;
    if v2 > area { area = v2; }
    if v3 > area { area = v3; }
    if v4 > area { area = v4; }

    proof {
        assert forall|c1: int, r1: int, c2: int, r2: int| #![auto]
            0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b
            && is_valid_window(a as int, b as int, c1, r1, c2, r2)
            && window_avoids_dead(c1, r1, c2, r2, x as int, y as int)
            implies window_area(c1, r1, c2, r2) <= area by
        {
            window_bound_lemma(a as int, b as int, c1, r1, c2, r2, x as int, y as int);
        }

        if v1 >= v2 && v1 >= v3 && v1 >= v4 && v1 > 0 {
            assert(x >= 1);
            assert(is_valid_window(a as int, b as int, 0, 0, (x - 1) as int, (b - 1) as int));
            assert(window_avoids_dead(0, 0, (x - 1) as int, (b - 1) as int, x as int, y as int));
            assert(window_area(0, 0, (x - 1) as int, (b - 1) as int) == x * b) by(nonlinear_arith)
                requires x >= 1, b >= 1;
        } else if v2 >= v1 && v2 >= v3 && v2 >= v4 && v2 > 0 {
            assert(y >= 1);
            assert(is_valid_window(a as int, b as int, 0, 0, (a - 1) as int, (y - 1) as int));
            assert(window_avoids_dead(0, 0, (a - 1) as int, (y - 1) as int, x as int, y as int));
            assert(window_area(0, 0, (a - 1) as int, (y - 1) as int) == y * a) by(nonlinear_arith)
                requires y >= 1, a >= 1;
        } else if v3 >= v1 && v3 >= v2 && v3 >= v4 && v3 > 0 {
            assert(x + 1 <= a - 1) by(nonlinear_arith)
                requires v3 > 0, v3 == (a - x - 1) * b, b >= 1, 0 <= x < a;
            assert(is_valid_window(a as int, b as int, (x + 1) as int, 0, (a - 1) as int, (b - 1) as int));
            assert(window_avoids_dead((x + 1) as int, 0, (a - 1) as int, (b - 1) as int, x as int, y as int));
            assert(window_area((x + 1) as int, 0, (a - 1) as int, (b - 1) as int) == (a - x - 1) * b) by(nonlinear_arith)
                requires x + 1 <= a - 1, b >= 1;
        } else if v4 > 0 {
            assert(y + 1 <= b - 1) by(nonlinear_arith)
                requires v4 > 0, v4 == (b - y - 1) * a, a >= 1, 0 <= y < b;
            assert(is_valid_window(a as int, b as int, 0, (y + 1) as int, (a - 1) as int, (b - 1) as int));
            assert(window_avoids_dead(0, (y + 1) as int, (a - 1) as int, (b - 1) as int, x as int, y as int));
            assert(window_area(0, (y + 1) as int, (a - 1) as int, (b - 1) as int) == (b - y - 1) * a) by(nonlinear_arith)
                requires y + 1 <= b - 1, a >= 1;
        }
    }

    area
}

fn main() {}

} // verus!

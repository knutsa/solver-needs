use vstd::prelude::*;

verus! {

// --- Specification ---

pub open spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}

pub open spec fn order_flipped(a: int, b: int, pa: int, pb: int) -> bool {
    (a < b && pa > pb) || (a > b && pa < pb)
}

pub open spec fn swap_cost(a: int, b: int, pa: int, pb: int) -> int {
    abs_val(a - pa) + abs_val(b - pb) - (if order_flipped(a, b, pa, pb) { 1 as int } else { 0 as int })
}

pub open spec fn is_achievable(n: int, x: int, a: int, b: int, d: int) -> bool
    recommends n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
{
    exists|pa: int, pb: int|
        1 <= pa <= n && 1 <= pb <= n
        && pa != pb && abs_val(pa - pb) == d && swap_cost(a, b, pa, pb) <= x
}

pub open spec fn is_max_distance(n: int, x: int, a: int, b: int, d: int) -> bool
    recommends n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0
{
    is_achievable(n, x, a, b, d)
    && forall|pa: int, pb: int|
        1 <= pa <= n && 1 <= pb <= n && pa != pb && swap_cost(a, b, pa, pb) <= x
        ==> abs_val(pa - pb) <= d
}

// --- Implementation ---

fn two_rival_students(n: i64, x: i64, a: i64, b: i64) -> (distance: i64)
    requires
        n >= 2 && 1 <= a <= n && 1 <= b <= n && a != b && x >= 0,
    ensures
        is_max_distance(n as int, x as int, a as int, b as int, distance as int),
{
    let mut la: i64 = a;
    let mut lb: i64 = b;
    let mut rx: i64 = x;

    if la > lb {
        let tmp = la;
        la = lb;
        lb = tmp;
    }

    let ghost oa: int = la as int;
    let ghost ob: int = lb as int;

    let da: i64 = if la - 1 < rx { la - 1 } else { rx };
    la = la - da;
    rx = rx - da;
    let db: i64 = if n - lb < rx { n - lb } else { rx };
    lb = lb + db;
    let distance: i64 = lb - la;

    // Key properties
    assert(1 <= la && la <= n && 1 <= lb && lb <= n && la < lb);
    assert(da >= 0 && db >= 0 && da + db <= x);
    assert(distance as int == ob - oa + da as int + db as int);

    // --- Prove IsAchievable ---
    proof {
        if a < b {
            assert(oa == a as int && ob == b as int);
            assert(la as int == a as int - da as int && lb as int == b as int + db as int);
            assert(abs_val(a as int - la as int) == da as int);
            assert(abs_val(b as int - lb as int) == db as int);
            assert(!order_flipped(a as int, b as int, la as int, lb as int));
            assert(swap_cost(a as int, b as int, la as int, lb as int) == da as int + db as int);
            assert(la != lb);
            assert(abs_val(la as int - lb as int) == distance as int);
        } else {
            assert(a > b);
            assert(oa == b as int && ob == a as int);
            assert(lb as int == a as int + db as int && la as int == b as int - da as int);
            assert(abs_val(a as int - lb as int) == db as int);
            assert(abs_val(b as int - la as int) == da as int);
            assert(!order_flipped(a as int, b as int, lb as int, la as int));
            assert(swap_cost(a as int, b as int, lb as int, la as int) == da as int + db as int);
            assert(lb != la);
            assert(abs_val(lb as int - la as int) == distance as int);
        }
    }
    assert(is_achievable(n as int, x as int, a as int, b as int, distance as int));

    // --- Prove upper bound ---
    proof {
        assert forall|pa: int, pb: int|
            1 <= pa <= n && 1 <= pb <= n && pa != pb && swap_cost(a as int, b as int, pa, pb) <= x as int
            implies abs_val(pa - pb) <= distance as int
        by {
            if (da + db) < x {
                // Budget not exhausted => hit both boundaries
                assert(da as int == oa - 1);
                assert(la as int == 1);
                assert(db as int == n as int - ob);
                assert(lb as int == n as int);
                assert(distance as int == n as int - 1);
                // |pa - pb| <= n - 1 since 1 <= pa, pb <= n
            } else {
                // Full budget used
                assert(da as int + db as int == x as int);
                if a < b {
                    assert(distance as int == (b as int - a as int) + x as int);
                    if pa <= pb {
                        assert(!order_flipped(a as int, b as int, pa, pb));
                        assert(swap_cost(a as int, b as int, pa, pb) == abs_val(a as int - pa) + abs_val(b as int - pb));
                        assert(a as int - pa <= abs_val(a as int - pa));
                        assert(pb - b as int <= abs_val(b as int - pb));
                        assert(pb - pa <= abs_val(a as int - pa) + (b as int - a as int) + abs_val(b as int - pb));
                        assert(pb - pa <= x as int + (b as int - a as int));
                        assert(abs_val(pa - pb) == pb - pa);
                    } else {
                        assert(order_flipped(a as int, b as int, pa, pb));
                        assert(swap_cost(a as int, b as int, pa, pb) == abs_val(a as int - pa) + abs_val(b as int - pb) - 1);
                        assert(pa - a as int <= abs_val(a as int - pa));
                        assert(b as int - pb <= abs_val(b as int - pb));
                        assert(pa - pb <= abs_val(a as int - pa) + abs_val(b as int - pb) - (b as int - a as int));
                        assert(pa - pb <= x as int + 1 - (b as int - a as int));
                        assert(pa - pb <= x as int);
                        assert(abs_val(pa - pb) == pa - pb);
                        assert(x as int <= distance as int);
                    }
                } else {
                    assert(a > b);
                    assert(distance as int == (a as int - b as int) + x as int);
                    if pa >= pb {
                        assert(!order_flipped(a as int, b as int, pa, pb));
                        assert(swap_cost(a as int, b as int, pa, pb) == abs_val(a as int - pa) + abs_val(b as int - pb));
                        assert(pa - a as int <= abs_val(a as int - pa));
                        assert(b as int - pb <= abs_val(b as int - pb));
                        assert(pa - pb <= abs_val(a as int - pa) + (a as int - b as int) + abs_val(b as int - pb));
                        assert(pa - pb <= x as int + (a as int - b as int));
                        assert(abs_val(pa - pb) == pa - pb);
                    } else {
                        assert(order_flipped(a as int, b as int, pa, pb));
                        assert(swap_cost(a as int, b as int, pa, pb) == abs_val(a as int - pa) + abs_val(b as int - pb) - 1);
                        assert(a as int - pa <= abs_val(a as int - pa));
                        assert(pb - b as int <= abs_val(b as int - pb));
                        assert(pb - pa <= abs_val(a as int - pa) + abs_val(b as int - pb) - (a as int - b as int));
                        assert(pb - pa <= x as int + 1 - (a as int - b as int));
                        assert(pb - pa <= x as int);
                        assert(abs_val(pa - pb) == pb - pa);
                        assert(x as int <= distance as int);
                    }
                }
            }
        }
    }

    distance
}

fn main() {}

} // verus!

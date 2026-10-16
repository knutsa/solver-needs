use vstd::prelude::*;

verus! {

spec fn valid_assignment(x: int, y: int, a: int, b: int, c: int, d: int, k: int) -> bool {
    x >= 0 && y >= 0 && x * c >= a && y * d >= b && x + y <= k
}

spec fn feasible(a: int, b: int, c: int, d: int, k: int) -> bool {
    exists|x: int, y: int| valid_assignment(x, y, a, b, c, d, k)
}

proof fn mul_le(a: int, b: int, c: int)
    requires
        a <= b,
        c >= 0,
    ensures
        a * c <= b * c,
{
    assert(a * c <= b * c) by (nonlinear_arith)
        requires a <= b, c >= 0;
}

proof fn ceil_div_lower(a: int, c: int)
    requires
        a >= 1,
        c >= 1,
    ensures
        ((a + c - 1) / c) * c >= a,
        (a + c - 1) / c >= 0,
{
    let q = (a + c - 1) / c;
    let r = (a + c - 1) % c;
    assert(q * c + r == a + c - 1) by (nonlinear_arith)
        requires q == (a + c - 1) / c, r == (a + c - 1) % c, c >= 1, a >= 1;
    assert(r >= 0) by (nonlinear_arith)
        requires r == (a + c - 1) % c, c >= 1, a >= 1;
    assert(r <= c - 1) by (nonlinear_arith)
        requires r == (a + c - 1) % c, c >= 1, a >= 1;
    // q * c = a + c - 1 - r >= a + c - 1 - (c - 1) = a
    assert(q * c >= a) by (nonlinear_arith)
        requires q * c + r == a + c - 1, r <= c - 1, r >= 0, c >= 1, a >= 1;
    assert(q >= 0) by (nonlinear_arith)
        requires q * c >= a, a >= 1, c >= 1;
}

proof fn ceil_div_minimal(a: int, c: int, x: int)
    requires
        a >= 1,
        c >= 1,
        x >= 0,
        x * c >= a,
    ensures
        x >= (a + c - 1) / c,
{
    let q = (a + c - 1) / c;
    let r = (a + c - 1) % c;
    assert(q * c + r == a + c - 1) by (nonlinear_arith)
        requires q == (a + c - 1) / c, r == (a + c - 1) % c, c >= 1, a >= 1;
    assert(r >= 0) by (nonlinear_arith)
        requires r == (a + c - 1) % c, c >= 1, a >= 1;
    assert(r <= c - 1) by (nonlinear_arith)
        requires r == (a + c - 1) % c, c >= 1, a >= 1;

    // Proof by contradiction: if x < q then x <= q - 1
    // (q-1) * c = q*c - c = a + c - 1 - r - c = a - 1 - r <= a - 1
    // x * c <= (q-1) * c <= a - 1 < a, contradicting x * c >= a
    if x < q {
        assert((q - 1) * c == a - 1 - r) by (nonlinear_arith)
            requires q * c + r == a + c - 1, c >= 1;
        assert((q - 1) * c <= a - 1) by (nonlinear_arith)
            requires (q - 1) * c == a - 1 - r, r >= 0;
        assert(x <= q - 1) by (nonlinear_arith)
            requires x < q;
        assert(x * c <= (q - 1) * c) by (nonlinear_arith)
            requires x <= q - 1, c >= 1;
        assert(x * c <= a - 1) by (nonlinear_arith)
            requires x * c <= (q - 1) * c, (q - 1) * c <= a - 1;
        assert(false) by (nonlinear_arith)
            requires x * c <= a - 1, x * c >= a;
    }
}

fn pens_and_pencils(a: i64, b: i64, c: i64, d: i64, k: i64) -> (result: (i64, i64))
    requires
        a >= 1,
        b >= 1,
        c >= 1,
        d >= 1,
        k >= 1,
        // bounds to prevent overflow
        a as int + c as int - 1 <= i64::MAX as int,
        b as int + d as int - 1 <= i64::MAX as int,
    ensures
        feasible(a as int, b as int, c as int, d as int, k as int) ==>
            valid_assignment(result.0 as int, result.1 as int,
                             a as int, b as int, c as int, d as int, k as int),
        !feasible(a as int, b as int, c as int, d as int, k as int) ==> result.0 == -1i64,
{
    // Use i128 to avoid overflow
    let a_w = a as i128;
    let b_w = b as i128;
    let c_w = c as i128;
    let d_w = d as i128;
    let k_w = k as i128;

    let pens_w = (a_w + c_w - 1) / c_w;
    let pencils_w = (b_w + d_w - 1) / d_w;

    proof {
        ceil_div_lower(a as int, c as int);
        ceil_div_lower(b as int, d as int);
    }

    if pens_w + pencils_w <= k_w {
        // pens_w and pencils_w fit within i64 since they're <= k which is i64
        let pens = pens_w as i64;
        let pencils = pencils_w as i64;
        proof {
            // pens and pencils form a valid assignment
            assert(valid_assignment(pens_w as int, pencils_w as int, a as int, b as int, c as int, d as int, k as int));
        }
        return (pens, pencils);
    } else {
        proof {
            // For any x0, y0 that satisfy the individual constraints, x0 >= pens and y0 >= pencils,
            // so x0 + y0 >= pens + pencils > k, meaning no valid assignment exists.
            assert forall|x0: int, y0: int| !valid_assignment(x0, y0, a as int, b as int, c as int, d as int, k as int) by {
                if x0 >= 0 && y0 >= 0 && x0 * (c as int) >= a as int && y0 * (d as int) >= b as int {
                    ceil_div_minimal(a as int, c as int, x0);
                    ceil_div_minimal(b as int, d as int, y0);
                    assert(x0 >= pens_w as int);
                    assert(y0 >= pencils_w as int);
                    assert(x0 + y0 >= pens_w as int + pencils_w as int);
                    assert(pens_w as int + pencils_w as int > k as int);
                }
            };
            assert(!feasible(a as int, b as int, c as int, d as int, k as int));
        }
        return (-1, 0);
    }
}

fn main() {}

} // verus!

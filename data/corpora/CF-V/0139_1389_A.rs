use vstd::prelude::*;

verus! {

// ghost function GCD
spec fn gcd(a: int, b: int) -> int
    recommends a > 0, b >= 0,
    decreases b, when b >= 0 via gcd_decreases
{
    if b == 0 { a } else { gcd(b, a % b) }
}

#[via_fn]
proof fn gcd_decreases(a: int, b: int)
{
    // when b > 0, a % b < b
    assert(b > 0 ==> (a % b >= 0 && a % b < b)) by(nonlinear_arith);
}

// Prove GCD is positive
proof fn gcd_positive(a: int, b: int)
    requires a > 0, b >= 0,
    ensures gcd(a, b) > 0,
    decreases b,
{
    if b == 0 {
    } else {
        assert(a % b >= 0 && a % b < b) by(nonlinear_arith)
            requires a > 0, b > 0;
        gcd_positive(b, a % b);
    }
}

// ghost function LCM
spec fn lcm(a: int, b: int) -> int
    recommends a > 0, b > 0,
{
    (a / gcd(a, b)) * b
}

// ghost predicate ValidPair
spec fn valid_pair(x: int, y: int, l: int, r: int) -> bool
    recommends l >= 1,
{
    l <= x && x < y && y <= r && l <= lcm(x, y) && lcm(x, y) <= r
}

// helper: does x have a valid partner y in [x+1, r]?
spec fn has_partner(x: int, l: int, r: int) -> bool
    recommends l >= 1,
{
    exists|y: int| x + 1 <= y && y <= r && #[trigger] valid_pair(x, y, l, r)
}

// ghost predicate PairExists
spec fn pair_exists(l: int, r: int) -> bool
    recommends l >= 1,
{
    exists|x: int| l <= x && x <= r && #[trigger] has_partner(x, l, r)
}

proof fn product_non_neg(a: int, b: int)
    requires a >= 0, b >= 0,
    ensures a * b >= 0,
{
    assert(a * b >= 0) by(nonlinear_arith)
        requires a >= 0, b >= 0;
}

proof fn sum_divisible(a: int, b: int, g: int)
    requires
        g > 0,
        a % g == 0,
        b % g == 0,
    ensures (a + b) % g == 0,
{
    let k1 = a / g;
    let k2 = b / g;
    assert(a == k1 * g) by(nonlinear_arith)
        requires a % g == 0, g > 0, k1 == a / g;
    assert(b == k2 * g) by(nonlinear_arith)
        requires b % g == 0, g > 0, k2 == b / g;
    assert(a + b == (k1 + k2) * g) by(nonlinear_arith)
        requires a == k1 * g, b == k2 * g;
    assert((a + b) % g == 0) by(nonlinear_arith)
        requires a + b == (k1 + k2) * g, g > 0;
}

proof fn diff_divisible(a: int, b: int, g: int)
    requires
        g > 0,
        a % g == 0,
        b % g == 0,
    ensures (a - b) % g == 0,
{
    let k1 = a / g;
    let k2 = b / g;
    assert(a == k1 * g) by(nonlinear_arith)
        requires a % g == 0, g > 0, k1 == a / g;
    assert(b == k2 * g) by(nonlinear_arith)
        requires b % g == 0, g > 0, k2 == b / g;
    assert(a - b == (k1 - k2) * g) by(nonlinear_arith)
        requires a == k1 * g, b == k2 * g;
    assert((a - b) % g == 0) by(nonlinear_arith)
        requires a - b == (k1 - k2) * g, g > 0;
}

proof fn multiple_of_multiple(q: int, b: int, g: int)
    requires
        g > 0,
        b % g == 0,
    ensures (q * b) % g == 0,
    decreases (if q >= 0 { q } else { -q }),
{
    if q == 0 {
        assert(q * b == 0) by(nonlinear_arith)
            requires q == 0;
    } else if q > 0 {
        multiple_of_multiple(q - 1, b, g);
        assert(q * b == (q - 1) * b + b) by(nonlinear_arith)
            requires q > 0;
        sum_divisible((q - 1) * b, b, g);
    } else {
        multiple_of_multiple(q + 1, b, g);
        assert(q * b == (q + 1) * b - b) by(nonlinear_arith)
            requires q < 0;
        diff_divisible((q + 1) * b, b, g);
    }
}

proof fn gcd_divides_both(a: int, b: int)
    requires a > 0, b > 0,
    ensures
        a % gcd(a, b) == 0,
        b % gcd(a, b) == 0,
    decreases b,
{
    reveal_with_fuel(gcd, 2);
    if a % b == 0 {
        // gcd(a, b) = gcd(b, a % b) = gcd(b, 0) = b
        assert(a % b == 0);
        // b divides a, so a % b == 0, and gcd(a, b) = b
        assert(b % b == 0) by(nonlinear_arith)
            requires b > 0;
    } else {
        let r = a % b;
        assert(r > 0 && r < b) by(nonlinear_arith)
            requires a > 0, b > 0, a % b != 0, r == a % b;
        gcd_divides_both(b, r);
        let g = gcd(a, b);
        gcd_positive(a, b);
        assert(g > 0);
        // gcd(a, b) = gcd(b, r), so g divides b and r
        assert(b % g == 0);
        assert(r % g == 0);
        let q_val = a / b;
        assert(a == q_val * b + r) by(nonlinear_arith)
            requires a > 0, b > 0, q_val == a / b, r == a % b;
        multiple_of_multiple(q_val, b, g);
        sum_divisible(q_val * b, r, g);
    }
}

proof fn gcd_of_double_reverse(a: int)
    requires a > 0,
    ensures gcd(2 * a, a) == a,
{
    reveal_with_fuel(gcd, 2);
    assert((2 * a) % a == 0) by(nonlinear_arith)
        requires a > 0;
    // gcd(2*a, a) = gcd(a, (2*a) % a) = gcd(a, 0) = a
}

proof fn gcd_of_doubled(a: int)
    requires a > 0,
    ensures gcd(a, 2 * a) == a,
{
    reveal_with_fuel(gcd, 2);
    assert(a % (2 * a) == a) by(nonlinear_arith)
        requires a > 0;
    // gcd(a, 2*a) = gcd(2*a, a % (2*a)) = gcd(2*a, a)
    gcd_of_double_reverse(a);
}

proof fn lcm_lower_bound(x: int, y: int)
    requires x > 0, y > x,
    ensures lcm(x, y) >= 2 * x,
{
    gcd_divides_both(x, y);
    let g = gcd(x, y);
    gcd_positive(x, y);
    assert(x % g == 0);
    assert(y % g == 0);

    diff_divisible(y, x, g);
    assert((y - x) % g == 0);
    assert(y - x > 0);
    // y - x >= g since (y - x) % g == 0, y - x > 0, g > 0
    assert(y - x >= g) by(nonlinear_arith)
        requires (y - x) % g == 0, y - x > 0, g > 0;

    let a = x / g;
    assert(a * g == x) by(nonlinear_arith)
        requires x % g == 0, g > 0, a == x / g;
    assert(a >= 1) by(nonlinear_arith)
        requires a * g == x, x > 0, g > 0;
    assert(lcm(x, y) == a * y);

    // a * y >= a * (x + g): from y >= x + g and a >= 0
    assert(y - (x + g) >= 0);
    product_non_neg(a, y - (x + g));
    assert(a * (y - (x + g)) >= 0);
    assert(a * y - a * (x + g) == a * (y - (x + g))) by(nonlinear_arith)
        requires a >= 1;
    assert(a * y >= a * (x + g));

    // a * (x + g) == a * x + a * g == a * x + x
    assert(a * (x + g) == a * x + a * g) by(nonlinear_arith)
        requires a >= 1;
    assert(a * y >= a * x + x);

    // a * x >= x: from a >= 1, x > 0
    product_non_neg(a - 1, x);
    assert((a - 1) * x >= 0);
    assert(a * x - x == (a - 1) * x) by(nonlinear_arith)
        requires a >= 1;
    assert(a * x >= x);
    assert(a * x + x >= 2 * x) by(nonlinear_arith)
        requires a * x >= x;
}

fn lcm_problem(l: i64, r: i64) -> (result: (i64, i64))
    requires
        l >= 1,
        r >= l,
        l as int * 2 <= i64::MAX,
    ensures
        (result.0 == -1 && result.1 == -1) || valid_pair(result.0 as int, result.1 as int, l as int, r as int),
        (result.0 == -1 && result.1 == -1) <==> !pair_exists(l as int, r as int),
{
    if l * 2 > r {
        proof {
            assert forall|xi: int, yi: int| l as int <= xi && xi < yi && yi <= r as int
                implies !valid_pair(xi, yi, l as int, r as int) by {
                lcm_lower_bound(xi, yi);
            }
            assert(!pair_exists(l as int, r as int));
        }
        (-1i64, -1i64)
    } else {
        proof {
            gcd_of_doubled(l as int);
            assert(gcd(l as int, 2 * l as int) == l as int);
            assert(l as int / l as int == 1) by(nonlinear_arith)
                requires l >= 1;
            assert(lcm(l as int, 2 * l as int) == 2 * l as int) by(nonlinear_arith)
                requires gcd(l as int, 2 * l as int) == l as int, l >= 1;
            assert(valid_pair(l as int, 2 * l as int, l as int, r as int));
            // witness for pair_exists
            assert(has_partner(l as int, l as int, r as int)) by {
                let y = 2 * l as int;
                assert(valid_pair(l as int, y, l as int, r as int));
            }
            assert(pair_exists(l as int, r as int)) by {
                assert(has_partner(l as int, l as int, r as int));
            }
        }
        (l, l * 2)
    }
}

} // verus!

fn main() {}

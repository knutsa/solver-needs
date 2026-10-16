use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;
use vstd::arithmetic::mul::*;

verus! {

// ghost function Gcd(a: int, b: int): int
spec fn gcd(a: int, b: int) -> int
    recommends a > 0 && b > 0,
    decreases b,
    when b > 0
{
    if a % b == 0 { b }
    else { gcd(b, a % b) }
}

// Helper: a % b is in [0, b) when a >= 0 and b > 0
// This is needed for termination reasoning
proof fn mod_bound(a: int, b: int)
    requires
        a > 0,
        b > 0,
    ensures
        0 <= a % b < b,
{
    lemma_mod_pos_bound(a, b);
}

// Helper: a % b == a when 0 < a < b
proof fn small_mod(a: int, b: int)
    requires
        0 < a,
        a < b,
    ensures
        a % b == a,
{
    lemma_small_mod(a as nat, b as nat);
}

// Helper: b % a == 0 implies b == a * (b / a)
proof fn div_mod_identity(a: int, b: int)
    requires
        a > 0,
        b > 0,
        b % a == 0,
    ensures
        b == a * (b / a),
{
    lemma_fundamental_div_mod(b, a);
}

// lemma MulLeMonotone(c: int, a: int, b: int)
proof fn mul_le_monotone(c: int, a: int, b: int)
    requires
        c > 0,
        a <= b,
    ensures
        c * a <= c * b,
    decreases c,
{
    if c == 1 {
        // base: 1 * a <= 1 * b trivially
    } else {
        mul_le_monotone(c - 1, a, b);
        // We have (c-1)*a <= (c-1)*b
        // Need: c*a <= c*b, i.e. (c-1)*a + a <= (c-1)*b + b
        lemma_mul_is_distributive_add(c - 1, a, 0);
        assert((c - 1) * a + a == (c - 1) * a + 1 * a);
        lemma_mul_is_distributive_add_other_way(a, c - 1, 1);
        assert((c - 1 + 1) * a == (c - 1) * a + 1 * a);
        assert(c * a == (c - 1) * a + a);

        lemma_mul_is_distributive_add_other_way(b, c - 1, 1);
        assert(c * b == (c - 1) * b + b);
    }
}

// lemma GcdBound(a: int, b: int)
proof fn gcd_bound(a: int, b: int)
    requires
        0 < a,
        a < b,
    ensures
        gcd(a, b) * 2 <= b,
    decreases b, a,
{
    small_mod(a, b);
    assert(a % b == a);
    assert(gcd(a, b) == gcd(b, a));

    let r = b % a;
    lemma_mod_pos_bound(b, a);
    if r == 0 {
        assert(gcd(b, a) == a);
        let k = b / a;
        div_mod_identity(a, b);
        assert(b == a * k);
        // Need k >= 2. Since b > a > 0 and b = a * k, k >= 2
        lemma_div_pos_is_pos(b, a);
        assert(k >= 0);
        // b > a = a * 1, so a * k > a * 1, so k > 1 (k >= 2)
        if k < 2 {
            if k == 0 {
                assert(b == a * 0);
                lemma_mul_basics(a);
                assert(false);
            } else {
                assert(k == 1);
                assert(b == a * 1);
                lemma_mul_basics(a);
                assert(b == a);
                assert(false); // contradicts a < b
            }
        }
        assert(k >= 2);
        mul_le_monotone(a, 2, k);
        assert(a * 2 <= a * k);
        assert(a * 2 <= b);
        lemma_mul_is_commutative(a, 2);
        // gcd(b,a) == a, so gcd(a,b) * 2 = a * 2 <= b
    } else {
        assert(0 < r && r < a);
        // gcd(b, a) = gcd(a, r) since b % a == r != 0
        assert(gcd(b, a) == gcd(a, r));
        // Since 0 < r < a, gcd(r, a) is well-defined
        // a % r: need to show a % a == a when r < a... no.
        // Actually gcd(a, r) checks if a % r == 0
        // We need: gcd(r, a) == gcd(a, r)
        // For that, r % a == r since 0 < r < a
        small_mod(r, a);
        assert(r % a == r);
        assert(gcd(r, a) == gcd(a, r));
        // Now call recursive bound
        gcd_bound(r, a);
        // This gives gcd(r, a) * 2 <= a
        // Since a < b, gcd(r, a) * 2 <= a < b, so gcd(r, a) * 2 <= b
        // But we need gcd(a, b) * 2 <= b
        // gcd(a, b) == gcd(b, a) == gcd(a, r) == gcd(r, a)
        // So gcd(a, b) * 2 = gcd(r, a) * 2 <= a < b
    }
}

// method MaximumGCD(n: int) returns (result: int)
fn maximum_gcd(n: i64) -> (result: i64)
    requires
        n >= 2,
    ensures
        exists|a: int, b: int| 1 <= a && a < n && a < b && b <= n && #[trigger] gcd(a, b) == result,
        forall|a: int, b: int| 1 <= a && a < n && a < b && b <= n ==> #[trigger] gcd(a, b) <= result,
{
    let result = n / 2;

    proof {
        let wa = (n / 2) as int;
        let wb = 2 * wa;

        assert(1 <= wa) by {
            assert(n >= 2);
        };
        assert(wa < n) by {
            lemma_div_basics_5(n as int, 2);
            assert(n / 2 <= n);
            // n/2 < n when n >= 2
            if wa >= n {
                lemma_fundamental_div_mod(n as int, 2);
                assert(n == 2 * (n / 2) + n % 2);
                lemma_mod_pos_bound(n as int, 2);
                // n = 2*wa + r where 0 <= r < 2
                // if wa >= n, then 2*wa >= 2*n, and 2*n > n + n % 2 when n >= 2
                assert(false);
            }
        };

        // wb = 2 * wa = 2 * (n/2)
        // Need wb <= n
        lemma_fundamental_div_mod(n as int, 2);
        assert(n == 2 * (n / 2) + n % 2);
        lemma_mod_pos_bound(n as int, 2);
        assert(wb == 2 * wa);
        assert(wb <= n as int);
        assert(wa < wb);

        // gcd(wa, wb): wa divides wb since wb = 2*wa
        // wb % wa == 0
        assert(wb % wa == 0) by {
            assert(wb == wa * 2);
            lemma_mod_multiples_basic(2, wa);
            assert((2 * wa) % wa == 0);
            lemma_mul_is_commutative(2, wa);
        };
        assert(gcd(wa, wb) == gcd(wb, wa)) by {
            small_mod(wa, wb);
        };
        assert(gcd(wb, wa) == wa);

        // Witness for existential
        assert(gcd(wa, wb) == result);

        // Upper bound proof
        assert forall|ai: int, bi: int| 1 <= ai && ai < n && ai < bi && bi <= n implies #[trigger] gcd(ai, bi) <= result by {
            gcd_bound(ai, bi);
            // gcd(ai, bi) * 2 <= bi <= n
            // So gcd(ai, bi) <= n/2 = result
            // But we need to be more precise: gcd(ai,bi)*2 <= bi <= n
            // So gcd(ai,bi) <= n/2 = result
            lemma_fundamental_div_mod(n as int, 2);
        };
    }

    result
}

fn main() {}

} // verus!

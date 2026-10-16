use vstd::prelude::*;

verus! {

spec fn fits_side_by_side(w1: int, h1: int, w2: int, h2: int, s: int) -> bool {
    w1 + w2 <= s && h1 <= s && h2 <= s
}

spec fn fits_stacked(w1: int, h1: int, w2: int, h2: int, s: int) -> bool {
    w1 <= s && w2 <= s && h1 + h2 <= s
}

spec fn can_fit_in_square(a: int, b: int, s: int) -> bool {
    fits_side_by_side(a, b, a, b, s) || fits_stacked(a, b, a, b, s) ||
    fits_side_by_side(a, b, b, a, s) || fits_stacked(a, b, b, a, s) ||
    fits_side_by_side(b, a, a, b, s) || fits_stacked(b, a, a, b, s) ||
    fits_side_by_side(b, a, b, a, s) || fits_stacked(b, a, b, a, s)
}

spec fn is_minimal_side(a: int, b: int, s: int) -> bool {
    can_fit_in_square(a, b, s) &&
    forall|s_prime: int| 1 <= s_prime && s_prime < s ==> !can_fit_in_square(a, b, s_prime)
}

fn minimal_square(a: i64, b: i64) -> (area: i64)
    requires
        1 <= a,
        1 <= b,
        a <= 1_000_000_000,
        b <= 1_000_000_000,
    ensures
        exists|s: int| 1 <= s && area as int == s * s && is_minimal_side(a as int, b as int, s),
{
    let lo: i64 = if a < b { a } else { b };
    let hi: i64 = if a < b { b } else { a };
    let val: i64 = if 2 * lo > hi { 2 * lo } else { hi };

    proof {
        let a_int = a as int;
        let b_int = b as int;
        let val_int = val as int;

        assert(val_int >= 1);

        // Overflow bound: val <= 2 * 10^9, so val * val <= 4 * 10^18 < i64::MAX
        assert(val_int <= 2_000_000_000int);
        assert(val_int * val_int <= 4_000_000_000_000_000_000int) by (nonlinear_arith)
            requires val_int >= 0 && val_int <= 2_000_000_000int;

        // Show can_fit_in_square(a, b, val)
        if a_int <= b_int {
            assert(2 * a_int <= val_int && b_int <= val_int);
            assert(fits_side_by_side(a_int, b_int, a_int, b_int, val_int));
        } else {
            assert(2 * b_int <= val_int && a_int <= val_int);
            assert(fits_side_by_side(b_int, a_int, b_int, a_int, val_int));
        }
        assert(can_fit_in_square(a_int, b_int, val_int));

        // Key inequality: val <= a + b
        assert(val_int <= a_int + b_int);

        // Show minimality: no smaller square works
        assert forall|s_prime: int| 1 <= s_prime && s_prime < val_int
            implies !can_fit_in_square(a_int, b_int, s_prime) by {
            // s' < val <= a+b, so mixed-orientation configs fail
            assert(!(a_int + b_int <= s_prime));

            // Mixed-orientation disjuncts all require a+b <= s'
            assert(!fits_side_by_side(a_int, b_int, b_int, a_int, s_prime));
            assert(!fits_stacked(a_int, b_int, b_int, a_int, s_prime));
            assert(!fits_side_by_side(b_int, a_int, a_int, b_int, s_prime));
            assert(!fits_stacked(b_int, a_int, a_int, b_int, s_prime));

            if a_int <= b_int {
                // val = max(2a, b). Since a <= b: 2b >= 2a and 2b >= b, so 2b >= val
                assert(2 * b_int >= val_int);
                assert(!(2 * a_int <= s_prime && b_int <= s_prime));
                assert(!(a_int <= s_prime && 2 * b_int <= s_prime));
                assert(!(2 * b_int <= s_prime && a_int <= s_prime));
                assert(!(b_int <= s_prime && 2 * a_int <= s_prime));

                assert(!fits_side_by_side(a_int, b_int, a_int, b_int, s_prime));
                assert(!fits_stacked(a_int, b_int, a_int, b_int, s_prime));
                assert(!fits_side_by_side(b_int, a_int, b_int, a_int, s_prime));
                assert(!fits_stacked(b_int, a_int, b_int, a_int, s_prime));
            } else {
                // val = max(2b, a). Since a > b: 2a > 2b and 2a >= a, so 2a >= val
                assert(2 * a_int >= val_int);
                assert(!(2 * a_int <= s_prime && b_int <= s_prime));
                assert(!(a_int <= s_prime && 2 * b_int <= s_prime));
                assert(!(2 * b_int <= s_prime && a_int <= s_prime));
                assert(!(b_int <= s_prime && 2 * a_int <= s_prime));

                assert(!fits_side_by_side(a_int, b_int, a_int, b_int, s_prime));
                assert(!fits_stacked(a_int, b_int, a_int, b_int, s_prime));
                assert(!fits_side_by_side(b_int, a_int, b_int, a_int, s_prime));
                assert(!fits_stacked(b_int, a_int, b_int, a_int, s_prime));
            }
        };

        assert(is_minimal_side(a_int, b_int, val_int));
    }

    val * val
}

fn main() {}

} // verus!
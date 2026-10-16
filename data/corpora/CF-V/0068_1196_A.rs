use vstd::prelude::*;

verus! {

spec fn min_val(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

spec fn candies_after_division(ap: int, bp: int, sp: int, s: int) -> int {
    min_val(ap + s, bp + (sp - s))
}

spec fn is_achievable(a: int, b: int, c: int, result: int) -> bool {
    (exists|s: int| 0 <= s <= c && candies_after_division(a, b, c, s) == result)
    || (exists|s: int| 0 <= s <= b && candies_after_division(a, c, b, s) == result)
    || (exists|s: int| 0 <= s <= a && candies_after_division(b, c, a, s) == result)
}

spec fn is_optimal(a: int, b: int, c: int, result: int) -> bool {
    (forall|s: int| 0 <= s <= c ==> candies_after_division(a, b, c, s) <= result)
    && (forall|s: int| 0 <= s <= b ==> candies_after_division(a, c, b, s) <= result)
    && (forall|s: int| 0 <= s <= a ==> candies_after_division(b, c, a, s) <= result)
}

proof fn lemma_min_le_half_sum(x: int, y: int)
    ensures min_val(x, y) <= (x + y) / 2
{
    assert(2 * min_val(x, y) <= x + y);
}

fn three_piles_of_candies(a: i64, b: i64, c: i64) -> (max_candies: i64)
    requires
        a >= 0,
        b >= 0,
        c >= 0,
        a + b + c <= i64::MAX,
    ensures
        is_achievable(a as int, b as int, c as int, max_candies as int),
        is_optimal(a as int, b as int, c as int, max_candies as int),
{
    let max_candies = (a + b + c) / 2;

    proof {
        let a_ = a as int;
        let b_ = b as int;
        let c_ = c as int;
        let r = max_candies as int;

        assert(r == (a_ + b_ + c_) / 2);

        // Optimality: any valid split yields at most r
        // Key: candies_after_division sums to a+b+c, so min <= (a+b+c)/2 = r
        assert forall|s: int| 0 <= s <= c_ implies candies_after_division(a_, b_, c_, s) <= r by {
            lemma_min_le_half_sum(a_ + s, b_ + (c_ - s));
        };
        assert forall|s: int| 0 <= s <= b_ implies candies_after_division(a_, c_, b_, s) <= r by {
            lemma_min_le_half_sum(a_ + s, c_ + (b_ - s));
        };
        assert forall|s: int| 0 <= s <= a_ implies candies_after_division(b_, c_, a_, s) <= r by {
            lemma_min_le_half_sum(b_ + s, c_ + (a_ - s));
        };

        // Achievability: provide witness splitting the largest pile
        if a_ >= b_ && a_ >= c_ {
            // Split pile a; Alice takes b, Bob takes c; witness s = r - b
            assert(exists|s: int| 0 <= s <= a_ && candies_after_division(b_, c_, a_, s) == r) by {
                let s = r - b_;
                assert(0 <= s && s <= a_);
                assert(b_ + s == r);
                assert(c_ + (a_ - s) >= r);
                assert(candies_after_division(b_, c_, a_, s) == r);
            };
        } else if b_ >= a_ && b_ >= c_ {
            // Split pile b; Alice takes a, Bob takes c; witness s = r - a
            assert(exists|s: int| 0 <= s <= b_ && candies_after_division(a_, c_, b_, s) == r) by {
                let s = r - a_;
                assert(0 <= s && s <= b_);
                assert(a_ + s == r);
                assert(c_ + (b_ - s) >= r);
                assert(candies_after_division(a_, c_, b_, s) == r);
            };
        } else {
            // c is the maximum; split pile c; Alice takes a, Bob takes b; witness s = r - a
            assert(exists|s: int| 0 <= s <= c_ && candies_after_division(a_, b_, c_, s) == r) by {
                let s = r - a_;
                assert(c_ >= a_ && c_ >= b_);
                assert(0 <= s && s <= c_);
                assert(a_ + s == r);
                assert(b_ + (c_ - s) >= r);
                assert(candies_after_division(a_, b_, c_, s) == r);
            };
        }
    }

    max_candies
}

fn main() {}

} // verus!
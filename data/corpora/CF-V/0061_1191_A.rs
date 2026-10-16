use vstd::prelude::*;

verus! {

// Maps HP to a category rank per the problem statement:
//   A (hp % 4 == 1) = 3, B (hp % 4 == 3) = 2, C (hp % 4 == 2) = 1, D (hp % 4 == 0) = 0
spec fn category_rank(hp: int) -> int
{
    let r = hp % 4;
    if r == 1 { 3 }
    else if r == 3 { 2 }
    else if r == 2 { 1 }
    else { 0 }
}

// Maps HP to its category character per the problem statement.
spec fn category_char(hp: int) -> char
{
    let r = hp % 4;
    if r == 1 { 'A' }
    else if r == 3 { 'B' }
    else if r == 2 { 'C' }
    else { 'D' }
}

proof fn category_rank_bounded(hp: int)
    requires hp >= 1
    ensures 0 <= category_rank(hp) <= 3
{
}

// Helper spec fn to serve as trigger target
spec fn rank_at(x: int, delta: int) -> int {
    category_rank(x + delta)
}

fn tokitsukaze_and_enhancement(x: i64) -> (result: (i64, char))
    requires x >= 1i64
    ensures ({
        let (a, b) = result;
        &&& 0 <= a <= 2
        &&& b == category_char(x as int + a as int)
        &&& forall|delta: int| 0 <= delta <= 2 ==> #[trigger] rank_at(x as int, delta) <= rank_at(x as int, a as int)
        &&& forall|delta: int| 0 <= delta < a ==> #[trigger] rank_at(x as int, delta) < rank_at(x as int, a as int)
    })
{
    let r = x % 4;
    if r == 0 {
        proof {
            assert((x as int + 0) % 4 == 0) by(nonlinear_arith) requires x as int % 4 == 0, x >= 1;
            assert((x as int + 1) % 4 == 1) by(nonlinear_arith) requires x as int % 4 == 0, x >= 1;
            assert((x as int + 2) % 4 == 2) by(nonlinear_arith) requires x as int % 4 == 0, x >= 1;
            assert(category_rank(x as int + 0) == 0);
            assert(category_rank(x as int + 1) == 3);
            assert(category_rank(x as int + 2) == 1);
            assert forall|delta: int| 0 <= delta <= 2 implies #[trigger] rank_at(x as int, delta) <= rank_at(x as int, 1) by {
                assert(delta == 0 || delta == 1 || delta == 2);
            }
        }
        (1, 'A')
    } else if r == 1 {
        proof {
            assert((x as int + 0) % 4 == 1) by(nonlinear_arith) requires x as int % 4 == 1, x >= 1;
            assert((x as int + 1) % 4 == 2) by(nonlinear_arith) requires x as int % 4 == 1, x >= 1;
            assert((x as int + 2) % 4 == 3) by(nonlinear_arith) requires x as int % 4 == 1, x >= 1;
            assert(category_rank(x as int + 0) == 3);
            assert(category_rank(x as int + 1) == 1);
            assert(category_rank(x as int + 2) == 2);
            assert forall|delta: int| 0 <= delta <= 2 implies #[trigger] rank_at(x as int, delta) <= rank_at(x as int, 0) by {
                assert(delta == 0 || delta == 1 || delta == 2);
            }
        }
        (0, 'A')
    } else if r == 2 {
        proof {
            assert((x as int + 0) % 4 == 2) by(nonlinear_arith) requires x as int % 4 == 2, x >= 1;
            assert((x as int + 1) % 4 == 3) by(nonlinear_arith) requires x as int % 4 == 2, x >= 1;
            assert((x as int + 2) % 4 == 0) by(nonlinear_arith) requires x as int % 4 == 2, x >= 1;
            assert(category_rank(x as int + 0) == 1);
            assert(category_rank(x as int + 1) == 2);
            assert(category_rank(x as int + 2) == 0);
            assert forall|delta: int| 0 <= delta <= 2 implies #[trigger] rank_at(x as int, delta) <= rank_at(x as int, 1) by {
                assert(delta == 0 || delta == 1 || delta == 2);
            }
            assert forall|delta: int| 0 <= delta < 1 implies #[trigger] rank_at(x as int, delta) < rank_at(x as int, 1) by {
                assert(delta == 0);
            }
        }
        (1, 'B')
    } else {
        proof {
            assert(x as int % 4 == 3) by {
                assert(r == 3);
            }
            assert((x as int + 0) % 4 == 3) by(nonlinear_arith) requires x as int % 4 == 3, x >= 1;
            assert((x as int + 1) % 4 == 0) by(nonlinear_arith) requires x as int % 4 == 3, x >= 1;
            assert((x as int + 2) % 4 == 1) by(nonlinear_arith) requires x as int % 4 == 3, x >= 1;
            assert(category_rank(x as int + 0) == 2);
            assert(category_rank(x as int + 1) == 0);
            assert(category_rank(x as int + 2) == 3);
            assert forall|delta: int| 0 <= delta <= 2 implies #[trigger] rank_at(x as int, delta) <= rank_at(x as int, 2) by {
                assert(delta == 0 || delta == 1 || delta == 2);
            }
            assert forall|delta: int| 0 <= delta < 2 implies #[trigger] rank_at(x as int, delta) < rank_at(x as int, 2) by {
                assert(delta == 0 || delta == 1);
            }
        }
        (2, 'A')
    }
}

fn main() {}

} // verus!

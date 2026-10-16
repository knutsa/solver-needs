use vstd::prelude::*;

verus! {

spec fn valid_step(from: int, to: int) -> bool {
    (to > from && (to - from) % 2 == 1)
    ||
    (from - to >= 2 && (from - to) % 2 == 0)
}

spec fn reachable_in(a: int, b: int, steps: nat) -> bool
    decreases steps
{
    if steps == 0 {
        a == b
    } else if steps == 1 {
        valid_step(a, b)
    } else {
        exists|c: int| valid_step(a, c) && reachable_in(c, b, (steps - 1) as nat)
    }
}

fn add_odd_or_subtract_even(a: i64, b: i64) -> (moves: i64)
    requires
        a >= 1 && b >= 1,
    ensures
        0 <= moves <= 2,
        reachable_in(a as int, b as int, moves as nat),
        forall|k: int| 0 <= k < moves ==> !(#[trigger] reachable_in(a as int, b as int, k as nat)),
{
    if a == b {
        0
    } else if a % 2 == b % 2 && a > b {
        1
    } else if a % 2 != b % 2 && b > a {
        1
    } else {
        proof {
            let c: int = a as int + 1;
            assert(valid_step(a as int, c));
            assert(valid_step(c, b as int));
            assert(reachable_in(c, b as int, 1nat));
            assert(exists|cc: int| valid_step(a as int, cc) && reachable_in(cc, b as int, 1nat)) by {
                assert(valid_step(a as int, c) && reachable_in(c, b as int, 1nat));
            };
            assert(reachable_in(a as int, b as int, 2nat));
            assert(!reachable_in(a as int, b as int, 1nat));
        }
        2
    }
}

fn main() {}

} // verus!
use vstd::prelude::*;

verus! {

spec fn valid_move(n: int, x: int) -> bool {
    1 <= x && x < n && n % x != 0
}

spec fn reachable(start: int, target: int, steps: nat) -> bool
    decreases steps
{
    start >= 1 && target >= 1 &&
    (start == target ||
     (steps > 0 &&
      exists|x: int| #![trigger valid_move(start, x)]
          1 <= x && x < start && valid_move(start, x) &&
          reachable(start - x, target, (steps - 1) as nat)))
}

spec fn is_min_reachable(v: int, result: int) -> bool {
    v >= 1 && result >= 1 &&
    reachable(v, result, v as nat) &&
    forall|r: int| #![trigger reachable(v, r, v as nat)]
        1 <= r && r < result ==> !reachable(v, r, v as nat)
}

proof fn reachable_step(start: int, target: int, x: int, steps: nat)
    requires
        start >= 1,
        target >= 1,
        steps > 0,
        1 <= x < start,
        valid_move(start, x),
        reachable(start - x, target, (steps - 1) as nat),
    ensures
        reachable(start, target, steps),
{
    assert(valid_move(start, x));
}

fn definite_game(v: i64) -> (result: i64)
    requires v >= 1,
    ensures is_min_reachable(v as int, result as int),
{
    if v == 2 {
        proof {
            assert(reachable(2int, 2int, 2nat));
            assert(!valid_move(2int, 1int));
            assert(!reachable(2int, 1int, 2nat));
        }
        2
    } else if v == 1 {
        proof {
            assert(reachable(1int, 1int, 1nat));
        }
        1
    } else {
        proof {
            let v = v as int;
            assert(v >= 3);
            assert(v % (v - 1) != 0) by(nonlinear_arith)
                requires v >= 3
            {
            }
            assert(valid_move(v, v - 1));
            assert(reachable(1int, 1int, (v - 1) as nat));
            reachable_step(v, 1int, v - 1, v as nat);
        }
        1
    }
}

fn main() {}

} // verus!
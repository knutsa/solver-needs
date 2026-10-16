use vstd::prelude::*;

verus! {

// === Formal Specification ===

/// The number of adjacent-floor transitions between two floors.
spec fn floor_distance(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

/// Time for Masha to walk from floor x to floor y using the stairs.
spec fn stairs_time(x: int, y: int, t1: int) -> int {
    t1 * floor_distance(x, y)
}

/// Time for the elevator to travel from its current floor z to Masha's floor x.
spec fn elevator_approach_time(z: int, x: int, t2: int) -> int {
    t2 * floor_distance(z, x)
}

/// Time for the elevator to carry Masha from floor x to Egor's floor y.
spec fn elevator_ride_time(x: int, y: int, t2: int) -> int {
    t2 * floor_distance(x, y)
}

/// Time for door operations during elevator use.
spec fn door_ops_time(t3: int) -> int {
    3 * t3
}

/// Total time when using the elevator: approach + ride + door operations.
spec fn elevator_total_time(x: int, y: int, z: int, t2: int, t3: int) -> int {
    elevator_approach_time(z, x, t2) + elevator_ride_time(x, y, t2) + door_ops_time(t3)
}

/// Masha uses the elevator unless the stairs time is strictly less than the elevator time.
spec fn should_use_elevator(x: int, y: int, z: int, t1: int, t2: int, t3: int) -> bool {
    stairs_time(x, y, t1) >= elevator_total_time(x, y, z, t2, t3)
}

// === Method with specification ===

fn elevator_or_stairs(x: i64, y: i64, z: i64, t1: i64, t2: i64, t3: i64) -> (result: bool)
    requires
        x >= 1 && y >= 1 && z >= 1,
        x != y,
        t1 >= 1 && t2 >= 1 && t3 >= 1,
        // bounds to prevent overflow
        x <= 1_000_000 && y <= 1_000_000 && z <= 1_000_000,
        t1 <= 1_000_000 && t2 <= 1_000_000 && t3 <= 1_000_000,
    ensures
        result == should_use_elevator(x as int, y as int, z as int, t1 as int, t2 as int, t3 as int),
{
    let dxy: i64 = if x >= y { x - y } else { y - x };
    let dxz: i64 = if x >= z { x - z } else { z - x };

    proof {
        assert(dxy as int == floor_distance(x as int, y as int));
        assert(dxz as int == floor_distance(z as int, x as int));
    }

    assert(0 <= dxy <= 999_999) by {
        assert(dxy as int == floor_distance(x as int, y as int));
    };
    assert(0 <= dxz <= 999_999) by {
        assert(dxz as int == floor_distance(z as int, x as int));
    };

    assert(t1 * dxy <= 999_999_000_000i64) by(nonlinear_arith)
        requires 1 <= t1 <= 1_000_000, 0 <= dxy <= 999_999,
    ;
    let stairs = t1 * dxy;

    assert(t2 * dxy <= 999_999_000_000i64) by(nonlinear_arith)
        requires 1 <= t2 <= 1_000_000, 0 <= dxy <= 999_999,
    ;
    let t2_dxy = t2 * dxy;

    assert(t2 * dxz <= 999_999_000_000i64) by(nonlinear_arith)
        requires 1 <= t2 <= 1_000_000, 0 <= dxz <= 999_999,
    ;
    let t2_dxz = t2 * dxz;

    assert(t3 * 3 <= 3_000_000i64) by(nonlinear_arith)
        requires 1 <= t3 <= 1_000_000,
    ;
    let t3_3 = t3 * 3;

    assert(t2_dxy + t2_dxz + t3_3 <= 2_001_998_000_000i64) by(nonlinear_arith)
        requires
            0 <= t2_dxy <= 999_999_000_000i64,
            0 <= t2_dxz <= 999_999_000_000i64,
            0 <= t3_3 <= 3_000_000i64,
    ;
    let elev = t2_dxy + t2_dxz + t3_3;

    proof {
        assert(stairs as int == stairs_time(x as int, y as int, t1 as int));
        assert(t2 as int * dxz as int == elevator_approach_time(z as int, x as int, t2 as int));
        assert(t2 as int * dxy as int == elevator_ride_time(x as int, y as int, t2 as int));
        assert(t3 as int * 3 == door_ops_time(t3 as int));
        assert(elev as int == elevator_total_time(x as int, y as int, z as int, t2 as int, t3 as int));
    }

    stairs >= elev
}

fn main() {}

} // verus!

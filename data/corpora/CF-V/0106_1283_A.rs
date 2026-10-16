use vstd::prelude::*;

verus! {

spec fn valid_time(h: int, m: int) -> bool {
    0 <= h && h < 24 && 0 <= m && m < 60
}

spec fn minutes_since_midnight(h: int, m: int) -> int {
    h * 60 + m
}

spec fn clock_state_after(h: int, m: int, n: int) -> int {
    (minutes_since_midnight(h, m) + n) % 1440
}

spec fn reaches_midnight(h: int, m: int, n: int) -> bool {
    clock_state_after(h, m, n) == 0
}

fn minutes_before_new_year(h: i64, m: i64) -> (minutes: i64)
    requires
        valid_time(h as int, m as int),
    ensures
        1 <= minutes as int && minutes as int <= 1440,
        reaches_midnight(h as int, m as int, minutes as int),
        forall|k: int| 1 <= k && k < minutes as int ==> !reaches_midnight(h as int, m as int, k),
{
    let minutes: i64 = (23 - h) * 60 + (60 - m);

    proof {
        let hi = h as int;
        let mi = m as int;
        let msm = minutes_since_midnight(hi, mi);
        let mins = minutes as int;

        // Expand msm definition for nonlinear_arith
        assert(msm == hi * 60 + mi);

        // bounds on msm
        assert(0 <= msm && msm <= 1439) by(nonlinear_arith)
            requires 0 <= hi && hi < 24 && 0 <= mi && mi < 60 && msm == hi * 60 + mi
        {};

        // minutes == 1440 - msm
        assert(mins == 1440 - msm) by(nonlinear_arith)
            requires mins == (23 - hi) * 60 + (60 - mi) && msm == hi * 60 + mi
        {};

        // so 1 <= minutes <= 1440
        assert(1 <= mins && mins <= 1440);

        // reaches midnight: msm + minutes == 1440
        assert(msm + mins == 1440);
        assert((msm + mins) % 1440 == 0) by(nonlinear_arith)
            requires msm + mins == 1440
        {};
        assert(clock_state_after(hi, mi, mins) == 0);

        // minimality
        assert forall|k: int| 1 <= k && k < mins implies !reaches_midnight(hi, mi, k) by {
            let total = msm + k;
            assert(total == msm + k);
            assert(1 <= total && total < 1440) by(nonlinear_arith)
                requires 0 <= msm && msm <= 1439 && 1 <= k && k < mins && mins == 1440 - msm && total == msm + k
            {};
            assert(total % 1440 == total) by(nonlinear_arith)
                requires 1 <= total && total < 1440
            {};
            assert(total != 0);
            assert((msm + k) % 1440 != 0);
            assert(clock_state_after(hi, mi, k) != 0);
        };
    }
    minutes
}

fn main() {}

} // verus!

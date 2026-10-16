use vstd::prelude::*;

fn main() {}

verus! {

// A valid notebook purchase provides enough sheets of each color for n invitations.
// Each invitation requires 2 red, 5 green, and 8 blue sheets.
// Each notebook contains k sheets of a single color.
spec fn sufficient_notebooks(r: int, g: int, b: int, n: int, k: int) -> bool {
    r >= 0 && g >= 0 && b >= 0 &&
    r * k >= 2 * n &&
    g * k >= 5 * n &&
    b * k >= 8 * n
}

// m is the minimum non-negative integer such that m * k >= need:
// the fewest k-sheet notebooks to obtain at least `need` sheets.
spec fn is_min_cover(m: int, need: int, k: int) -> bool
    recommends k >= 1
{
    m >= 0 &&
    m * k >= need &&
    (m == 0 || (m - 1) * k < need)
}

// The minimum total notebooks for n invitations with k-sheet notebooks.
spec fn is_min_total_notebooks(total: int, n: int, k: int) -> bool
    recommends n >= 1 && k >= 1
{
    exists|r: nat, g: nat, b: nat|
        is_min_cover(r as int, 2 * n, k) &&
        is_min_cover(g as int, 5 * n, k) &&
        is_min_cover(b as int, 8 * n, k) &&
        sufficient_notebooks(r as int, g as int, b as int, n, k) &&
        total == r + g + b
}

proof fn ceil_div_is_min_cover(need: int, k: int)
    requires
        k >= 1,
        need >= 0,
    ensures
        is_min_cover((need + k - 1) / k, need, k),
{
    let m = (need + k - 1) / k;
    let rem = (need + k - 1) % k;

    assert(need + k - 1 == m * k + rem) by(nonlinear_arith)
        requires
            m == (need + k - 1) / k,
            rem == (need + k - 1) % k,
            k >= 1,
    ;

    assert(m * k == need + k - 1 - rem) by(nonlinear_arith)
        requires
            need + k - 1 == m * k + rem,
    ;

    assert(m * k >= need) by(nonlinear_arith)
        requires
            m * k == need + k - 1 - rem,
            rem >= 0,
            rem < k,
            k >= 1,
    ;

    // rem is in [0, k), so we need to establish its range
    assert(rem >= 0 && rem < k) by(nonlinear_arith)
        requires
            rem == (need + k - 1) % k,
            k >= 1,
    ;

    // m >= 0 since need >= 0 and k >= 1
    assert(m >= 0) by(nonlinear_arith)
        requires
            m == (need + k - 1) / k,
            need >= 0,
            k >= 1,
    ;

    if m > 0 {
        assert((m - 1) * k == need - 1 - rem) by(nonlinear_arith)
            requires
                m * k == need + k - 1 - rem,
                k >= 1,
        ;
        assert((m - 1) * k < need) by(nonlinear_arith)
            requires
                (m - 1) * k == need - 1 - rem,
                rem >= 0,
        ;
    }
}

fn petya_and_origami(n: i64, k: i64) -> (notebooks: i64)
    requires
        n >= 1,
        k >= 1,
        // Overflow bounds: the intermediate computations must fit in i64
        n as int * 8 + k as int - 1 <= i64::MAX as int,
        // The result must fit in i64
        ((n as int * 2 + k as int - 1) / k as int +
         (n as int * 5 + k as int - 1) / k as int +
         (n as int * 8 + k as int - 1) / k as int) <= i64::MAX as int,
    ensures
        is_min_total_notebooks(notebooks as int, n as int, k as int),
{
    let km1 = k - 1;
    let n2 = n * 2;
    let n5 = n * 5;
    let n8 = n * 8;
    let r = (n2 + km1) / k;
    let g = (n5 + km1) / k;
    let b = (n8 + km1) / k;

    proof {
        ceil_div_is_min_cover(2 * (n as int), k as int);
        ceil_div_is_min_cover(5 * (n as int), k as int);
        ceil_div_is_min_cover(8 * (n as int), k as int);

        assert(is_min_cover(r as int, 2 * (n as int), k as int));
        assert(is_min_cover(g as int, 5 * (n as int), k as int));
        assert(is_min_cover(b as int, 8 * (n as int), k as int));
        assert(sufficient_notebooks(r as int, g as int, b as int, n as int, k as int));

        // Witness for the existential
        assert(is_min_total_notebooks((r + g + b) as int, n as int, k as int));
    }

    r + g + b
}

} // verus!

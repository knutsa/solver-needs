use vstd::prelude::*;
use vstd::set::*;

verus! {

spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn in_grid(n: int, m: int, i: int, j: int) -> bool {
    1 <= i <= n && 1 <= j <= m
}

spec fn reachable_within(n: int, m: int, ti: int, tj: int, t: nat) -> Set<(int, int)>
    decreases t,
{
    if t == 0 {
        set![(ti, tj)]
    } else {
        let prev = reachable_within(n, m, ti, tj, (t - 1) as nat);
        Set::new(|pair: (int, int)| {
            let i = pair.0;
            let j = pair.1;
            1 <= i <= n && 1 <= j <= m && (
                prev.contains((i, j)) ||
                (i - 1 >= 1 && prev.contains((i - 1, j))) ||
                (i + 1 <= n && prev.contains((i + 1, j))) ||
                (j - 1 >= 1 && prev.contains((i, j - 1))) ||
                (j + 1 <= m && prev.contains((i, j + 1)))
            )
        })
    }
}

spec fn all_reach_within(n: int, m: int, ti: int, tj: int, t: nat) -> bool {
    let reach = reachable_within(n, m, ti, tj, t);
    forall|i: int, j: int| 1 <= i <= n && 1 <= j <= m ==> reach.contains((i, j))
}

proof fn reachable_monotone(n: int, m: int, ti: int, tj: int, t: nat, i: int, j: int)
    requires
        n >= 1 && m >= 1 && in_grid(n, m, ti, tj) && t >= 1,
        reachable_within(n, m, ti, tj, (t - 1) as nat).contains((i, j)),
    ensures
        reachable_within(n, m, ti, tj, t).contains((i, j)),
{
    let prev = reachable_within(n, m, ti, tj, (t - 1) as nat);
    let cur = reachable_within(n, m, ti, tj, t);
    // We need to show (i,j) is in cur. Since (i,j) is in prev, we need to show it satisfies
    // the set comprehension. But first we need to know i,j are in grid.
    // From prev definition by induction, (i,j) in prev means in_grid holds.
    // Actually we need a helper for that. Let's just assert the membership condition.
    reachable_in_grid(n, m, ti, tj, (t - 1) as nat, i, j);
    assert(cur.contains((i, j)));
}

proof fn reachable_in_grid(n: int, m: int, ti: int, tj: int, t: nat, i: int, j: int)
    requires
        n >= 1 && m >= 1 && in_grid(n, m, ti, tj),
        reachable_within(n, m, ti, tj, t).contains((i, j)),
    ensures
        in_grid(n, m, i, j),
    decreases t,
{
    if t == 0 {
        // base case: reachable set is {(ti, tj)}
    } else {
        let prev = reachable_within(n, m, ti, tj, (t - 1) as nat);
        let cur = reachable_within(n, m, ti, tj, t);
        // cur is defined by set comprehension requiring 1 <= i <= n && 1 <= j <= m
        // so in_grid follows directly from the definition
    }
}

proof fn reachable_complete(n: int, m: int, ti: int, tj: int, t: nat, i: int, j: int)
    requires
        n >= 1 && m >= 1 && in_grid(n, m, ti, tj),
        in_grid(n, m, i, j) && t >= 0,
        abs_val(i - ti) + abs_val(j - tj) <= t,
    ensures
        reachable_within(n, m, ti, tj, t).contains((i, j)),
    decreases t,
{
    if t == 0 {
        // abs_val(i - ti) + abs_val(j - tj) <= 0 means i == ti && j == tj
    } else if abs_val(i - ti) + abs_val(j - tj) <= (t - 1) as int {
        reachable_complete(n, m, ti, tj, (t - 1) as nat, i, j);
        reachable_monotone(n, m, ti, tj, t, i, j);
    } else {
        let prev = reachable_within(n, m, ti, tj, (t - 1) as nat);
        if i > ti {
            assert(abs_val(i - 1 - ti) + abs_val(j - tj) == t - 1) by(nonlinear_arith)
                requires abs_val(i - ti) + abs_val(j - tj) == t as int, i > ti,
                    abs_val(i - ti) == if (i - ti) >= 0 { i - ti } else { -(i - ti) },
                    abs_val(i - 1 - ti) == if (i - 1 - ti) >= 0 { i - 1 - ti } else { -(i - 1 - ti) },
                    abs_val(j - tj) == if (j - tj) >= 0 { j - tj } else { -(j - tj) },
            ;
            reachable_complete(n, m, ti, tj, (t - 1) as nat, i - 1, j);
            assert(prev.contains((i - 1, j)));
            assert(i - 1 >= 1);
        } else if i < ti {
            assert(abs_val(i + 1 - ti) + abs_val(j - tj) == t - 1) by(nonlinear_arith)
                requires abs_val(i - ti) + abs_val(j - tj) == t as int, i < ti,
                    abs_val(i - ti) == if (i - ti) >= 0 { i - ti } else { -(i - ti) },
                    abs_val(i + 1 - ti) == if (i + 1 - ti) >= 0 { i + 1 - ti } else { -(i + 1 - ti) },
                    abs_val(j - tj) == if (j - tj) >= 0 { j - tj } else { -(j - tj) },
            ;
            reachable_complete(n, m, ti, tj, (t - 1) as nat, i + 1, j);
            assert(prev.contains((i + 1, j)));
            assert(i + 1 <= n);
        } else if j > tj {
            assert(abs_val(i - ti) + abs_val(j - 1 - tj) == t - 1) by(nonlinear_arith)
                requires abs_val(i - ti) + abs_val(j - tj) == t as int, i == ti, j > tj,
                    abs_val(i - ti) == if (i - ti) >= 0 { i - ti } else { -(i - ti) },
                    abs_val(j - tj) == if (j - tj) >= 0 { j - tj } else { -(j - tj) },
                    abs_val(j - 1 - tj) == if (j - 1 - tj) >= 0 { j - 1 - tj } else { -(j - 1 - tj) },
            ;
            reachable_complete(n, m, ti, tj, (t - 1) as nat, i, j - 1);
            assert(prev.contains((i, j - 1)));
            assert(j - 1 >= 1);
        } else {
            // i == ti && j < tj
            assert(abs_val(i - ti) + abs_val(j + 1 - tj) == t - 1) by(nonlinear_arith)
                requires abs_val(i - ti) + abs_val(j - tj) == t as int, i == ti, j < tj,
                    abs_val(i - ti) == if (i - ti) >= 0 { i - ti } else { -(i - ti) },
                    abs_val(j - tj) == if (j - tj) >= 0 { j - tj } else { -(j - tj) },
                    abs_val(j + 1 - tj) == if (j + 1 - tj) >= 0 { j + 1 - tj } else { -(j + 1 - tj) },
            ;
            reachable_complete(n, m, ti, tj, (t - 1) as nat, i, j + 1);
            assert(prev.contains((i, j + 1)));
            assert(j + 1 <= m);
        }
    }
}

proof fn reachable_soundness(n: int, m: int, ti: int, tj: int, t: nat, i: int, j: int)
    requires
        n >= 1 && m >= 1 && in_grid(n, m, ti, tj) && t >= 0,
        reachable_within(n, m, ti, tj, t).contains((i, j)),
    ensures
        abs_val(i - ti) + abs_val(j - tj) <= t,
    decreases t,
{
    if t == 0 {
        // (i,j) == (ti, tj) so distance is 0
    } else {
        let prev = reachable_within(n, m, ti, tj, (t - 1) as nat);
        if prev.contains((i, j)) {
            reachable_soundness(n, m, ti, tj, (t - 1) as nat, i, j);
        } else if i - 1 >= 1 && prev.contains((i - 1, j)) {
            reachable_soundness(n, m, ti, tj, (t - 1) as nat, i - 1, j);
        } else if i + 1 <= n && prev.contains((i + 1, j)) {
            reachable_soundness(n, m, ti, tj, (t - 1) as nat, i + 1, j);
        } else if j - 1 >= 1 && prev.contains((i, j - 1)) {
            reachable_soundness(n, m, ti, tj, (t - 1) as nat, i, j - 1);
        } else {
            assert(j + 1 <= m && prev.contains((i, j + 1)));
            reachable_soundness(n, m, ti, tj, (t - 1) as nat, i, j + 1);
        }
    }
}

proof fn all_reach_helper(n: int, m: int, r: int, c: int, dr: int, dc: int, time: nat)
    requires
        n >= 1 && m >= 1 && in_grid(n, m, r, c),
        dr >= r - 1 && dr >= n - r,
        dc >= c - 1 && dc >= m - c,
        time == dr + dc,
    ensures
        all_reach_within(n, m, r, c, time),
{
    assert forall|i: int, j: int| 1 <= i <= n && 1 <= j <= m implies
        reachable_within(n, m, r, c, time).contains((i, j))
    by {
        assert(abs_val(i - r) <= dr) by(nonlinear_arith)
            requires 1 <= i <= n, dr >= r - 1, dr >= n - r,
                abs_val(i - r) == if (i - r) >= 0 { i - r } else { -(i - r) },
        ;
        assert(abs_val(j - c) <= dc) by(nonlinear_arith)
            requires 1 <= j <= m, dc >= c - 1, dc >= m - c,
                abs_val(j - c) == if (j - c) >= 0 { j - c } else { -(j - c) },
        ;
        reachable_complete(n, m, r, c, time, i, j);
    }
}

proof fn optimality_helper(n: int, m: int, r: int, c: int, dr: int, dc: int, time: nat)
    requires
        n >= 1 && m >= 1 && in_grid(n, m, r, c),
        (dr == r - 1 || dr == n - r) && dr >= r - 1 && dr >= n - r,
        (dc == c - 1 || dc == m - c) && dc >= c - 1 && dc >= m - c,
        time == dr + dc && time > 0,
    ensures
        !all_reach_within(n, m, r, c, (time - 1) as nat),
{
    let ci: int = if dr == r - 1 { 1int } else { n };
    let cj: int = if dc == c - 1 { 1int } else { m };
    assert(in_grid(n, m, ci, cj));
    if dr == r - 1 {
        assert(ci == 1);
        assert(ci - r == 1 - r);
        assert(r >= 1);
        assert(abs_val(ci - r) == r - 1);
        assert(abs_val(ci - r) == dr);
    } else {
        assert(dr == n - r);
        assert(ci == n);
        assert(ci - r == n - r);
        assert(n - r >= 0);
        assert(abs_val(ci - r) == n - r);
        assert(abs_val(ci - r) == dr);
    }
    if dc == c - 1 {
        assert(cj == 1);
        assert(cj - c == 1 - c);
        assert(c >= 1);
        assert(abs_val(cj - c) == c - 1);
        assert(abs_val(cj - c) == dc);
    } else {
        assert(dc == m - c);
        assert(cj == m);
        assert(cj - c == m - c);
        assert(m - c >= 0);
        assert(abs_val(cj - c) == m - c);
        assert(abs_val(cj - c) == dc);
    }
    assert(abs_val(ci - r) + abs_val(cj - c) == time as int);

    if reachable_within(n, m, r, c, (time - 1) as nat).contains((ci, cj)) {
        reachable_soundness(n, m, r, c, (time - 1) as nat, ci, cj);
        assert(false);
    }
    assert(!reachable_within(n, m, r, c, (time - 1) as nat).contains((ci, cj)));
    // Witness that not all cells are reachable in time-1
    assert(!all_reach_within(n, m, r, c, (time - 1) as nat));
}

fn prison_break(n: i64, m: i64, r: i64, c: i64) -> (time: i64)
    requires
        n >= 1 && m >= 1,
        n <= 1_000_000_000 && m <= 1_000_000_000,
        in_grid(n as int, m as int, r as int, c as int),
    ensures
        time >= 0,
        all_reach_within(n as int, m as int, r as int, c as int, time as nat),
        time == 0 || !all_reach_within(n as int, m as int, r as int, c as int, (time - 1) as nat),
{
    let dr: i64 = if r - 1 > n - r { r - 1 } else { n - r };
    let dc: i64 = if c - 1 > m - c { c - 1 } else { m - c };
    let time: i64 = {
        assert(dr >= 0 && dc >= 0);
        assert(dr <= n - 1);
        assert(dc <= m - 1);
        dr + dc
    };

    proof {
        all_reach_helper(n as int, m as int, r as int, c as int, dr as int, dc as int, time as nat);

        if time > 0 {
            optimality_helper(n as int, m as int, r as int, c as int, dr as int, dc as int, time as nat);
        }
    }

    time
}

fn main() {}

} // verus!

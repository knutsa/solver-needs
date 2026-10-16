use vstd::prelude::*;

verus! {

// ── Helper functions ──

pub open spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}

pub open spec fn max_val(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

// ── Problem formalization ──

// Chebyshev (L∞) distance between two cells
pub open spec fn chebyshev_dist(r1: int, c1: int, r2: int, c2: int) -> int {
    max_val(abs_val(r1 - r2), abs_val(c1 - c2))
}

// A valid single king move: to an adjacent cell (8 directions) within an n×n board
pub open spec fn valid_king_step(r1: int, c1: int, r2: int, c2: int, n: int) -> bool {
    1 <= r1 <= n && 1 <= c1 <= n
    && 1 <= r2 <= n && 1 <= c2 <= n
    && abs_val(r1 - r2) <= 1 && abs_val(c1 - c2) <= 1
    && (r1 != r2 || c1 != c2)
}

// Greedy one step toward (tr, tc)
pub open spec fn step_toward_r(r: int, tr: int) -> int {
    r + (if tr > r { 1int } else if tr < r { -1int } else { 0int })
}

pub open spec fn step_toward_c(c: int, tc: int) -> int {
    c + (if tc > c { 1int } else if tc < c { -1int } else { 0int })
}

// EXISTENCE witness: the greedy step is a valid king move that reduces distance by 1
pub open spec fn greedy_step_valid(r: int, c: int, tr: int, tc: int, n: int) -> bool {
    1 <= r <= n && 1 <= c <= n && 1 <= tr <= n && 1 <= tc <= n
    && ((r == tr && c == tc)
        || (valid_king_step(r, c, step_toward_r(r, tr), step_toward_c(c, tc), n)
            && chebyshev_dist(step_toward_r(r, tr), step_toward_c(c, tc), tr, tc)
               == chebyshev_dist(r, c, tr, tc) - 1))
}

// OPTIMALITY: no single king step can reduce Chebyshev distance by more than 1.
pub open spec fn no_step_reduces_by_more_than_one(r: int, c: int, tr: int, tc: int) -> bool {
    forall|dr: int, dc: int|
        (-1 <= dr <= 1 && -1 <= dc <= 1)
        ==> #[trigger] chebyshev_dist(r + dr, c + dc, tr, tc) >= chebyshev_dist(r, c, tr, tc) - 1
}

// Turn structure
pub open spec fn arrival_turn(dist: int, moves_first: bool) -> int {
    if dist == 0 { 0 }
    else if moves_first { 2 * dist - 1 }
    else { 2 * dist }
}

// The correct winner
pub open spec fn correct_winner(winner: u8, n: int, x: int, y: int) -> bool
    recommends n >= 2 && 1 <= x <= n && 1 <= y <= n
{
    let white_dist = chebyshev_dist(1, 1, x, y);
    let black_dist = chebyshev_dist(n, n, x, y);
    let white_turn = arrival_turn(white_dist, true);
    let black_turn = arrival_turn(black_dist, false);
    // winner == 0 means White, winner == 1 means Black
    (winner == 0u8 <==> white_turn <= black_turn)
    && (winner == 1u8 <==> white_turn > black_turn)
}

// ── Lemmas ──

proof fn abs_triangle(a: int, d: int)
    requires -1 <= d <= 1,
    ensures abs_val(a + d) >= abs_val(a) - 1,
{
}

proof fn max_monotone(a: int, b: int, c: int, d: int)
    requires
        a >= c - 1,
        b >= d - 1,
    ensures max_val(a, b) >= max_val(c, d) - 1,
{
}

proof fn no_step_reduces_single(r: int, c: int, tr: int, tc: int, dr: int, dc: int)
    requires -1 <= dr <= 1 && -1 <= dc <= 1,
    ensures chebyshev_dist(r + dr, c + dc, tr, tc) >= chebyshev_dist(r, c, tr, tc) - 1,
{
    let a = r - tr;
    let b = c - tc;
    abs_triangle(a, dr);
    abs_triangle(b, dc);
    assert(r + dr - tr == a + dr);
    assert(c + dc - tc == b + dc);
    max_monotone(abs_val(a + dr), abs_val(b + dc), abs_val(a), abs_val(b));
}

proof fn no_step_reduces_lemma(r: int, c: int, tr: int, tc: int)
    ensures no_step_reduces_by_more_than_one(r, c, tr, tc),
{
    assert forall|dr: int, dc: int|
        (-1 <= dr <= 1 && -1 <= dc <= 1)
        implies #[trigger] chebyshev_dist(r + dr, c + dc, tr, tc) >= chebyshev_dist(r, c, tr, tc) - 1
    by {
        if -1 <= dr <= 1 && -1 <= dc <= 1 {
            no_step_reduces_single(r, c, tr, tc, dr, dc);
        }
    }
}

proof fn greedy_step_valid_lemma(r: int, c: int, tr: int, tc: int, n: int)
    requires 1 <= r <= n && 1 <= c <= n && 1 <= tr <= n && 1 <= tc <= n,
    ensures greedy_step_valid(r, c, tr, tc, n),
{
    if r != tr || c != tc {
        let p_r = step_toward_r(r, tr);
        let p_c = step_toward_c(c, tc);
        assert(1 <= p_r <= n);
        assert(1 <= p_c <= n);
    }
}

// ── Method with specification ──

fn kings_race(n: i64, x: i64, y: i64) -> (winner: u8)
    requires
        n >= 2 && 1 <= x <= n && 1 <= y <= n,
    ensures
        correct_winner(winner, n as int, x as int, y as int),
        greedy_step_valid(1, 1, x as int, y as int, n as int),
        greedy_step_valid(n as int, n as int, x as int, y as int, n as int),
        no_step_reduces_by_more_than_one(1, 1, x as int, y as int),
        no_step_reduces_by_more_than_one(n as int, n as int, x as int, y as int),
{
    let dx1: i64 = if x - 1 >= 0 { x - 1 } else { 1 - x };
    let dy1: i64 = if y - 1 >= 0 { y - 1 } else { 1 - y };
    let dist1: i64 = if dx1 >= dy1 { dx1 } else { dy1 };

    let dx2: i64 = if x - n >= 0 { x - n } else { n - x };
    let dy2: i64 = if y - n >= 0 { y - n } else { n - y };
    let dist2: i64 = if dx2 >= dy2 { dx2 } else { dy2 };

    assert(dist1 as int == chebyshev_dist(1, 1, x as int, y as int));
    assert(dist2 as int == chebyshev_dist(n as int, n as int, x as int, y as int));

    proof {
        greedy_step_valid_lemma(1, 1, x as int, y as int, n as int);
        greedy_step_valid_lemma(n as int, n as int, x as int, y as int, n as int);
        no_step_reduces_lemma(1, 1, x as int, y as int);
        no_step_reduces_lemma(n as int, n as int, x as int, y as int);
    }

    if dist1 <= dist2 {
        0u8 // White
    } else {
        1u8 // Black
    }
}

fn main() {}

} // verus!

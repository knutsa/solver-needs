use vstd::prelude::*;

verus! {

spec fn grid_view(grid: &Vec<Vec<char>>) -> Seq<Seq<char>> {
    grid@.map_values(|row: Vec<char>| row@)
}

spec fn seq_vec_view(s: Seq<Vec<char>>) -> Seq<Seq<char>> {
    s.map_values(|v: Vec<char>| v@)
}

spec fn rectangular(grid: Seq<Seq<char>>) -> bool {
    grid.len() > 0 &&
    forall|i: int| 0 <= i < grid.len() ==> (#[trigger] grid[i]).len() == grid[0].len()
}

spec fn has_star(grid: Seq<Seq<char>>) -> bool {
    exists|r: int| #![trigger grid[r]] 0 <= r < grid.len() &&
        exists|c: int| 0 <= c < grid[r].len() && grid[r][c] == '*'
}

spec fn is_sub_rectangle(
    grid: Seq<Seq<char>>, result: Seq<Seq<char>>,
    top: int, bottom: int, left: int, right: int,
) -> bool {
    0 <= top < bottom <= grid.len() as int &&
    0 <= left < right &&
    (forall|r: int| top <= r < bottom ==> right <= (#[trigger] grid[r]).len()) &&
    result.len() == bottom - top &&
    (forall|i: int| 0 <= i < bottom - top ==>
        (#[trigger] result[i]) =~= grid[top + i].subrange(left, right))
}

spec fn contains_all_shaded(
    grid: Seq<Seq<char>>,
    top: int, bottom: int, left: int, right: int,
) -> bool {
    forall|r: int, c: int|
        #![trigger grid[r][c]]
        0 <= r < grid.len() && 0 <= c < grid[r].len() && grid[r][c] == '*'
        ==> (top <= r < bottom && left <= c < right)
}

spec fn tight_bounds(
    grid: Seq<Seq<char>>,
    top: int, bottom: int, left: int, right: int,
) -> bool {
    0 <= top < bottom <= grid.len() as int &&
    0 <= left < right &&
    (forall|r: int| top <= r < bottom ==> right <= (#[trigger] grid[r]).len()) &&
    (exists|c: int| #![trigger grid[top][c]] left <= c < right && grid[top][c] == '*') &&
    (exists|c: int| #![trigger grid[bottom - 1][c]] left <= c < right && grid[bottom - 1][c] == '*') &&
    (exists|r: int| #![trigger grid[r][left]] top <= r < bottom && grid[r][left] == '*') &&
    (exists|r: int| #![trigger grid[r][right - 1]] top <= r < bottom && grid[r][right - 1] == '*')
}

spec fn is_minimal_bounding_box(
    grid: Seq<Seq<char>>, result: Seq<Seq<char>>,
    top: int, bottom: int, left: int, right: int,
) -> bool {
    is_sub_rectangle(grid, result, top, bottom, left, right) &&
    contains_all_shaded(grid, top, bottom, left, right) &&
    tight_bounds(grid, top, bottom, left, right)
}

proof fn grid_view_index(grid: &Vec<Vec<char>>, r: int)
    requires 0 <= r < grid@.len(),
    ensures grid_view(grid)[r] == grid@[r as int]@,
{}

fn scan_row_for_star(row: &Vec<char>, m: usize) -> (found: usize)
    requires row.len() == m, m > 0,
    ensures
        found < m ==> row@[found as int] == '*',
        found >= m ==> forall|c: int| 0 <= c < m as int ==> (#[trigger] row@[c]) != '*',
{
    let mut j: usize = 0;
    while j < m
        invariant
            0 <= j <= m, row.len() == m,
            forall|c: int| 0 <= c < j as int ==> (#[trigger] row@[c]) != '*',
        decreases m - j,
    {
        if row[j] == '*' { return j; }
        j = j + 1;
    }
    m
}

fn scan_col_for_star(grid: &Vec<Vec<char>>, col: usize, n: usize, m: usize) -> (found: usize)
    requires
        grid.len() == n, n > 0, 0 <= col < m,
        forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]).len() == m,
    ensures
        found < n ==> grid@[found as int]@[col as int] == '*',
        found >= n ==> forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]@)[col as int] != '*',
{
    let mut r: usize = 0;
    while r < n
        invariant
            0 <= r <= n, grid.len() == n, n > 0, 0 <= col < m,
            forall|rr: int| 0 <= rr < n as int ==> (#[trigger] grid@[rr]).len() == m,
            forall|rr: int| 0 <= rr < r as int ==> (#[trigger] grid@[rr]@)[col as int] != '*',
        decreases n - r,
    {
        if grid[r][col] == '*' { return r; }
        r = r + 1;
    }
    n
}

// Find first row with '*', scanning from start
fn find_top(grid: &Vec<Vec<char>>, n: usize, m: usize) -> (top: usize)
    requires
        grid.len() == n, n > 0, m > 0,
        forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]).len() == m,
        has_star(grid_view(grid)),
    ensures
        top < n,
        exists|c: int| 0 <= c < m as int && grid@[top as int]@[c] == '*',
        forall|r: int, c: int|
            #![trigger grid@[r]@[c]]
            (0 <= r < top as int && 0 <= c < m as int) ==> grid@[r]@[c] != '*',
{
    let mut top: usize = 0;
    while top < n
        invariant
            0 <= top <= n, grid.len() == n, n > 0, m > 0,
            forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]).len() == m,
            has_star(grid_view(grid)),
            forall|r: int, c: int|
                #![trigger grid@[r]@[c]]
                (0 <= r < top as int && 0 <= c < m as int) ==> grid@[r]@[c] != '*',
        decreases n - top,
    {
        let found = scan_row_for_star(&grid[top], m);
        if found < m {
            return top;
        }
        top = top + 1;
    }
    // Contradiction: all rows scanned, no star
    proof {
        assert(!has_star(grid_view(grid))) by {
            assert forall|r: int|
                #![trigger grid_view(grid)[r]]
                0 <= r < grid_view(grid).len()
            implies
                !(exists|c: int| 0 <= c < grid_view(grid)[r].len() && grid_view(grid)[r][c] == '*')
            by {
                grid_view_index(grid, r);
            };
        };
    }
    0  // unreachable
}

// Find last row with '*', scanning from end; must be >= start
fn find_bot(grid: &Vec<Vec<char>>, n: usize, m: usize, start: usize) -> (bot: usize)
    requires
        grid.len() == n, n > 0, m > 0,
        start < n,
        forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]).len() == m,
        exists|c: int| 0 <= c < m as int && grid@[start as int]@[c] == '*',
    ensures
        start <= bot && bot < n,
        exists|c: int| 0 <= c < m as int && grid@[bot as int]@[c] == '*',
        forall|r: int, c: int|
            #![trigger grid@[r]@[c]]
            (bot as int + 1 <= r && r < n as int && 0 <= c && c < m as int) ==> grid@[r]@[c] != '*',
{
    let mut bot: usize = n - 1;
    while bot > start
        invariant
            start <= bot && bot < n,
            grid.len() == n, n > 0, m > 0,
            start < n,
            forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]).len() == m,
            exists|c: int| 0 <= c < m as int && grid@[start as int]@[c] == '*',
            forall|r: int, c: int|
                #![trigger grid@[r]@[c]]
                (bot as int + 1 <= r && r < n as int && 0 <= c && c < m as int) ==> grid@[r]@[c] != '*',
        decreases bot - start,
    {
        let found = scan_row_for_star(&grid[bot], m);
        if found < m {
            return bot;
        }
        bot = bot - 1;
    }
    // bot == start, which has a star
    start
}

// Find first column with '*'
fn find_left(grid: &Vec<Vec<char>>, n: usize, m: usize) -> (left: usize)
    requires
        grid.len() == n, n > 0, m > 0,
        forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]).len() == m,
        has_star(grid_view(grid)),
    ensures
        left < m,
        exists|r: int| #![trigger grid@[r]@] 0 <= r < n as int && grid@[r]@[left as int] == '*',
        forall|r: int, c: int|
            #![trigger grid@[r]@[c]]
            (0 <= r < n as int && 0 <= c < left as int) ==> grid@[r]@[c] != '*',
{
    let mut left: usize = 0;
    while left < m
        invariant
            0 <= left <= m, grid.len() == n, n > 0, m > 0,
            forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]).len() == m,
            has_star(grid_view(grid)),
            forall|r: int, c: int|
                #![trigger grid@[r]@[c]]
                (0 <= r < n as int && 0 <= c < left as int) ==> grid@[r]@[c] != '*',
        decreases m - left,
    {
        let found = scan_col_for_star(grid, left, n, m);
        if found < n {
            return left;
        }
        left = left + 1;
    }
    proof {
        assert(!has_star(grid_view(grid))) by {
            assert forall|r: int|
                #![trigger grid_view(grid)[r]]
                0 <= r < grid_view(grid).len()
            implies
                !(exists|c: int| 0 <= c < grid_view(grid)[r].len() && grid_view(grid)[r][c] == '*')
            by {
                grid_view_index(grid, r);
            };
        };
    }
    0  // unreachable
}

// Find last column with '*', must be >= start
fn find_ri(grid: &Vec<Vec<char>>, n: usize, m: usize, start: usize) -> (ri: usize)
    requires
        grid.len() == n, n > 0, m > 0,
        start < m,
        forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]).len() == m,
        exists|r: int| #![trigger grid@[r]@] 0 <= r < n as int && grid@[r]@[start as int] == '*',
    ensures
        start <= ri && ri < m,
        exists|r: int| #![trigger grid@[r]@] 0 <= r < n as int && grid@[r]@[ri as int] == '*',
        forall|r: int, c: int|
            #![trigger grid@[r]@[c]]
            (0 <= r && r < n as int && ri as int + 1 <= c && c < m as int) ==> grid@[r]@[c] != '*',
{
    let mut ri: usize = m - 1;
    while ri > start
        invariant
            start <= ri && ri < m,
            grid.len() == n, n > 0, m > 0,
            start < m,
            forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]).len() == m,
            exists|r: int| #![trigger grid@[r]@] 0 <= r < n as int && grid@[r]@[start as int] == '*',
            forall|r: int, c: int|
                #![trigger grid@[r]@[c]]
                (0 <= r && r < n as int && ri as int + 1 <= c && c < m as int) ==> grid@[r]@[c] != '*',
        decreases ri - start,
    {
        let found = scan_col_for_star(grid, ri, n, m);
        if found < n {
            return ri;
        }
        ri = ri - 1;
    }
    start
}

fn letter(grid: &Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    requires
        rectangular(grid_view(grid)),
        has_star(grid_view(grid)),
        forall|r: int| 0 <= r < grid@.len() ==> (#[trigger] grid@[r]).len() == grid@[0].len(),
    ensures
        exists|top: int, bottom: int, left: int, right: int|
            #![trigger is_minimal_bounding_box(grid_view(grid), seq_vec_view(result@), top, bottom, left, right)]
            is_minimal_bounding_box(grid_view(grid), seq_vec_view(result@), top, bottom, left, right),
{
    let n = grid.len();
    let m = grid[0].len();

    let top = find_top(grid, n, m);
    let bot = find_bot(grid, n, m, top);
    let bottom = bot + 1;
    let left = find_left(grid, n, m);
    let ri = find_ri(grid, n, m, left);
    let right = ri + 1;

    // === PROOFS ===
    proof {
        let gv = grid_view(grid);

        assert forall|r: int| 0 <= r < n as int
            implies gv[r] == (#[trigger] grid@[r])@
        by { grid_view_index(grid, r); };

        // --- contains_all_shaded ---
        assert(contains_all_shaded(gv, top as int, bottom as int, left as int, right as int)) by {
            assert forall|r: int, c: int|
                #![trigger gv[r][c]]
                0 <= r < gv.len() && 0 <= c < gv[r].len() && gv[r][c] == '*'
            implies (top as int <= r < bottom as int && left as int <= c < right as int)
            by {
                grid_view_index(grid, r);
            };
        };

        // --- tight_bounds ---
        // top row has star, and that star is in [left..right) by contains_all_shaded
        let c_top = choose|c: int| 0 <= c < m as int && grid@[top as int]@[c] == '*';
        grid_view_index(grid, top as int);
        assert(gv[top as int][c_top] == '*');
        assert(left as int <= c_top < right as int);

        // bot row has star
        let c_bot = choose|c: int| 0 <= c < m as int && grid@[bot as int]@[c] == '*';
        grid_view_index(grid, bot as int);
        assert(gv[bot as int][c_bot] == '*');
        assert(left as int <= c_bot < right as int);

        // left col has star
        let r_left = choose|r: int| #![trigger grid@[r]@] 0 <= r < n as int && grid@[r]@[left as int] == '*';
        grid_view_index(grid, r_left);
        assert(gv[r_left][left as int] == '*');
        assert(top as int <= r_left < bottom as int);

        // ri col has star
        let r_right = choose|r: int| #![trigger grid@[r]@] 0 <= r < n as int && grid@[r]@[ri as int] == '*';
        grid_view_index(grid, r_right);
        assert(gv[r_right][ri as int] == '*');
        assert(top as int <= r_right < bottom as int);

        // Row widths
        assert forall|r: int| top as int <= r < bottom as int
            implies right as int <= (#[trigger] gv[r]).len()
        by { grid_view_index(grid, r); };

        // Assert each exists in tight_bounds with matching triggers
        assert(exists|c: int| #![trigger gv[top as int][c]] left as int <= c < right as int && gv[top as int][c] == '*') by {
            assert(gv[top as int][c_top] == '*');
        };
        assert(exists|c: int| #![trigger gv[bottom as int - 1][c]] left as int <= c < right as int && gv[bottom as int - 1][c] == '*') by {
            assert(gv[bot as int][c_bot] == '*');
            assert(bottom as int - 1 == bot as int);
        };
        assert(exists|r: int| #![trigger gv[r][left as int]] top as int <= r < bottom as int && gv[r][left as int] == '*') by {
            assert(gv[r_left][left as int] == '*');
        };
        assert(exists|r: int| #![trigger gv[r][right as int - 1]] top as int <= r < bottom as int && gv[r][right as int - 1] == '*') by {
            assert(right as int - 1 == ri as int);
            assert(gv[r_right][ri as int] == '*');
        };

        assert(tight_bounds(gv, top as int, bottom as int, left as int, right as int));
    }

    // === EXTRACT SUB-RECTANGLE ===
    let mut result: Vec<Vec<char>> = Vec::new();
    let mut idx: usize = top;
    while idx < bottom
        invariant
            top <= idx <= bottom, bottom <= n,
            grid.len() == n, m == grid@[0].len(),
            forall|r: int| 0 <= r < n as int ==> (#[trigger] grid@[r]).len() == m,
            left < right && right <= m,
            result@.len() == idx - top,
            forall|k: int| 0 <= k < (idx - top) as int ==>
                (#[trigger] result@[k])@ =~= grid@[top as int + k]@.subrange(left as int, right as int),
        decreases bottom - idx,
    {
        let row = &grid[idx];
        let mut sub: Vec<char> = Vec::new();
        let mut ci: usize = left;
        while ci < right
            invariant
                left <= ci <= right, right <= m, row.len() == m,
                sub@.len() == ci - left,
                forall|j: int| 0 <= j < (ci - left) as int ==>
                    sub@[j] == row@[left as int + j],
            decreases right - ci,
        {
            sub.push(row[ci]);
            ci = ci + 1;
        }
        proof {
            assert(sub@ =~= row@.subrange(left as int, right as int)) by {
                assert forall|j: int| #![auto] 0 <= j < (right - left) as int
                    implies sub@[j] == row@.subrange(left as int, right as int)[j]
                by {};
            };
        }
        result.push(sub);
        idx = idx + 1;
    }

    proof {
        let gv = grid_view(grid);
        let result_spec = seq_vec_view(result@);

        assert forall|r: int| top as int <= r < bottom as int
            implies right as int <= (#[trigger] gv[r]).len()
        by { grid_view_index(grid, r); };

        assert forall|i: int| 0 <= i < (bottom - top) as int
            implies (#[trigger] result_spec[i]) =~= gv[top as int + i].subrange(left as int, right as int)
        by {
            assert(result@[i]@ =~= grid@[top as int + i]@.subrange(left as int, right as int));
            grid_view_index(grid, top as int + i);
        };

        assert(is_sub_rectangle(gv, result_spec, top as int, bottom as int, left as int, right as int));
        assert(is_minimal_bounding_box(gv, result_spec, top as int, bottom as int, left as int, right as int));
    }

    result
}

fn main() {}

} // verus!

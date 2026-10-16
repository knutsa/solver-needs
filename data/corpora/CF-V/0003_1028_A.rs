use vstd::prelude::*;

verus! {

// Spec helper to convert Vec<Vec<char>> to Seq<Seq<char>>
pub closed spec fn grid_view(grid: &Vec<Vec<char>>) -> Seq<Seq<char>> {
    grid@.map_values(|v: Vec<char>| v@)
}

proof fn grid_view_properties(grid: &Vec<Vec<char>>)
    ensures
        grid_view(grid).len() == grid@.len(),
        forall|i: int| #![trigger grid_view(grid)[i]]
            0 <= i < grid@.len() as int ==> grid_view(grid)[i] =~= grid@[i]@,
{
    reveal(grid_view);
}

// Helper: check if a character appears in a sequence
pub open spec fn seq_contains_char(s: Seq<char>, c: char) -> bool {
    exists|j: int| 0 <= j < s.len() && s[j] == c
}

pub open spec fn valid_grid(n: int, m: int, grid: Seq<Seq<char>>) -> bool {
    n > 0 && m > 0 && grid.len() == n
    && (forall|i: int| #![trigger grid[i]] 0 <= i < n ==> grid[i].len() == m)
    && (forall|i: int, j: int| #![trigger grid[i][j]] 0 <= i < n && 0 <= j < m ==>
        grid[i][j] == 'W' || grid[i][j] == 'B')
}

pub open spec fn cell_in_square(i: int, j: int, cr: int, cc: int, half: int) -> bool {
    cr - half <= i && i <= cr + half
    && cc - half <= j && j <= cc + half
}

pub open spec fn is_black_square_centered_at(
    n: int, m: int, grid: Seq<Seq<char>>,
    cr: int, cc: int, half: int,
) -> bool
    recommends grid.len() == n && n > 0 && m > 0,
              forall|i: int| #![trigger grid[i]] 0 <= i < n ==> grid[i].len() == m,
{
    half >= 0
    && cr - half >= 0 && cr + half < n
    && cc - half >= 0 && cc + half < m
    && (forall|i: int, j: int|
        #![trigger grid[i][j]]
        0 <= i < n && 0 <= j < m ==>
            if cell_in_square(i, j, cr, cc, half) {
                grid[i][j] == 'B'
            } else {
                grid[i][j] == 'W'
            })
}

pub open spec fn has_black_square(n: int, m: int, grid: Seq<Seq<char>>) -> bool
    recommends grid.len() == n && n > 0 && m > 0,
              forall|i: int| #![trigger grid[i]] 0 <= i < n ==> grid[i].len() == m,
{
    exists|cr: int, cc: int, h: int|
        #![trigger is_black_square_centered_at(n, m, grid, cr, cc, h)]
        0 <= cr < n && 0 <= cc < m && h >= 0
        && is_black_square_centered_at(n, m, grid, cr, cc, h)
}

pub open spec fn has_centered_square_with_some_h(
    n: int, m: int, grid: Seq<Seq<char>>,
    cr: int, cc: int,
) -> bool {
    exists|h: int|
        #![trigger is_black_square_centered_at(n, m, grid, cr, cc, h)]
        h >= 0 && is_black_square_centered_at(n, m, grid, cr, cc, h)
}

proof fn row_outside_has_no_black(
    n: int, m: int, grid: Seq<Seq<char>>,
    cr: int, cc: int, half: int, i: int,
)
    requires
        grid.len() == n,
        n > 0,
        m > 0,
        forall|ii: int| #![trigger grid[ii]] 0 <= ii < n ==> grid[ii].len() == m,
        is_black_square_centered_at(n, m, grid, cr, cc, half),
        0 <= i < n,
        i < cr - half || i > cr + half,
    ensures
        !seq_contains_char(grid[i], 'B'),
{
    assert forall|j: int| 0 <= j < grid[i].len() implies grid[i][j] != 'B' by {
        assert(!cell_in_square(i, j, cr, cc, half));
    }
}

proof fn row_inside_has_black(
    n: int, m: int, grid: Seq<Seq<char>>,
    cr: int, cc: int, half: int, i: int,
)
    requires
        grid.len() == n,
        n > 0,
        m > 0,
        forall|ii: int| #![trigger grid[ii]] 0 <= ii < n ==> grid[ii].len() == m,
        is_black_square_centered_at(n, m, grid, cr, cc, half),
        0 <= i < n,
        cr - half <= i && i <= cr + half,
    ensures
        seq_contains_char(grid[i], 'B'),
{
    assert(cell_in_square(i, cc, cr, cc, half));
    assert(0 <= cc && cc < grid[i].len());
    assert(grid[i][cc] == 'B');
}

proof fn prove_exists_h(
    n: int, m: int, grid: Seq<Seq<char>>,
    cr: int, cc: int, half: int,
)
    requires
        grid.len() == n,
        n > 0,
        m > 0,
        half >= 0,
        forall|i: int| #![trigger grid[i]] 0 <= i < n ==> grid[i].len() == m,
        is_black_square_centered_at(n, m, grid, cr, cc, half),
    ensures
        has_centered_square_with_some_h(n, m, grid, cr, cc),
{
}

// Proof helper: seq_contains_char is preserved under =~=
proof fn seq_contains_preserved(s1: Seq<char>, s2: Seq<char>, c: char)
    requires s1 =~= s2
    ensures seq_contains_char(s1, c) == seq_contains_char(s2, c)
{
    assert(s1 =~= s2);
    if seq_contains_char(s1, c) {
        let j = choose|j: int| 0 <= j < s1.len() && s1[j] == c;
        assert(s2[j] == c);
    }
    if seq_contains_char(s2, c) {
        let j = choose|j: int| 0 <= j < s2.len() && s2[j] == c;
        assert(s1[j] == c);
    }
}

// Runtime helper to check if a row contains 'B'
fn row_contains_b(row: &Vec<char>) -> (result: bool)
    ensures result == seq_contains_char(row@, 'B'),
{
    let mut i: usize = 0;
    while i < row.len()
        invariant
            i <= row@.len(),
            forall|j: int| 0 <= j < i as int ==> row@[j] != 'B',
        decreases row@.len() - i,
    {
        if row[i] == 'B' {
            return true;
        }
        i = i + 1;
    }
    proof {
        assert forall|j: int| 0 <= j < row@.len() implies row@[j] != 'B' by {}
    }
    false
}

// The exec method that finds the square
fn find_square(n: i64, m: i64, grid: &Vec<Vec<char>>) -> (result: (i64, i64))
    requires
        valid_grid(n as int, m as int, grid_view(grid)),
        has_black_square(n as int, m as int, grid_view(grid)),
        n > 0,
        m > 0,
        grid@.len() == n,
        n < 0x4000_0000, // bound to prevent overflow
        m < 0x4000_0000,
    ensures ({
        let (r, c) = result;
        &&& 1 <= r <= n
        &&& 1 <= c <= m
        &&& has_centered_square_with_some_h(
            n as int, m as int,
            grid_view(grid),
            (r - 1) as int, (c - 1) as int,
        )
    }),
{
    let ghost sg: Seq<Seq<char>> = grid_view(grid);

    proof {
        grid_view_properties(grid);
    }

    // Extract ghost witnesses
    let ghost gcr_cc_h: (int, int, int) = choose|cr: int, cc: int, h: int|
        #![trigger is_black_square_centered_at(n as int, m as int, sg, cr, cc, h)]
        0 <= cr < n as int && 0 <= cc < m as int && h >= 0
        && is_black_square_centered_at(n as int, m as int, sg, cr, cc, h);
    let ghost gcr: int = gcr_cc_h.0;
    let ghost gcc: int = gcr_cc_h.1;
    let ghost gh: int = gcr_cc_h.2;

    proof {
        assert(has_black_square(n as int, m as int, sg));
        assert(0 <= gcr < n as int);
        assert(0 <= gcc < m as int);
        assert(gh >= 0);
        assert(is_black_square_centered_at(n as int, m as int, sg, gcr, gcc, gh));
    }

    // Loop 1: find first row with 'B'
    let mut ly: i64 = 0;
    let grid_len = grid.len() as i64;

    while ly < grid_len && !row_contains_b(&grid[ly as usize])
        invariant
            0 <= ly <= gcr - gh,
            grid_len == n,
            grid_len == grid@.len(),
            sg == grid_view(grid),
            valid_grid(n as int, m as int, sg),
            is_black_square_centered_at(n as int, m as int, sg, gcr, gcc, gh),
            0 <= gcr < n as int,
            0 <= gcc < m as int,
            gh >= 0,
            n < 0x4000_0000i64,
            forall|idx: int| #![trigger grid_view(grid)[idx]]
                0 <= idx < grid@.len() as int ==> grid_view(grid)[idx] =~= grid@[idx]@,
        decreases gcr - gh - ly,
    {
        proof {
            // The row at gcr - gh contains 'B' in spec_grid
            row_inside_has_black(n as int, m as int, sg, gcr, gcc, gh, gcr - gh);
            // So ly < gcr - gh (otherwise loop would have found 'B')
            // But we also need: row_contains_b on grid@[ly] returns false means spec_grid[ly] has no 'B'
            // This follows because grid@[ly]@ =~= sg[ly]
            seq_contains_preserved(grid@[ly as int]@, sg[ly as int], 'B');
        }
        ly = ly + 1;
    }

    proof {
        if ly < gcr - gh {
            // Loop exited because row_contains_b returned true
            // But row_outside_has_no_black says spec_grid[ly] has no 'B'
            row_outside_has_no_black(n as int, m as int, sg, gcr, gcc, gh, ly as int);
            seq_contains_preserved(grid@[ly as int]@, sg[ly as int], 'B');
            assert(false);
        }
        assert(ly == gcr - gh);
    }

    // Loop 2: find first row after ly without 'B'
    let mut ry: i64 = ly + 1;
    while ry < grid_len && row_contains_b(&grid[ry as usize])
        invariant
            ry > gcr - gh,
            ry <= gcr + gh + 1,
            grid_len == n,
            grid_len == grid@.len(),
            sg == grid_view(grid),
            valid_grid(n as int, m as int, sg),
            is_black_square_centered_at(n as int, m as int, sg, gcr, gcc, gh),
            0 <= gcr < n as int,
            0 <= gcc < m as int,
            gh >= 0,
            ly == gcr - gh,
            n < 0x4000_0000i64,
            forall|idx: int| #![trigger grid_view(grid)[idx]]
                0 <= idx < grid@.len() as int ==> grid_view(grid)[idx] =~= grid@[idx]@,
        decreases gcr + gh + 1 - ry,
    {
        proof {
            if ry > gcr + gh {
                row_outside_has_no_black(n as int, m as int, sg, gcr, gcc, gh, ry as int);
                seq_contains_preserved(grid@[ry as int]@, sg[ry as int], 'B');
                assert(false);
            }
        }
        ry = ry + 1;
    }

    proof {
        if ry <= gcr + gh {
            row_inside_has_black(n as int, m as int, sg, gcr, gcc, gh, ry as int);
            seq_contains_preserved(grid@[ry as int]@, sg[ry as int], 'B');
            assert(false);
        }
        assert(ry == gcr + gh + 1);
    }

    // Loop 3: find first 'B' column in row ly
    let ly_row = &grid[ly as usize];
    let mut lx: i64 = 0;
    let row_len = ly_row.len() as i64;

    proof {
        // Establish row_len == m
        assert(grid_view(grid)[ly as int] =~= grid@[ly as int]@);
        assert(sg[ly as int].len() == m as int);
        assert(grid@[ly as int]@.len() == m as int);
    }

    while lx < row_len && ly_row[lx as usize] != 'B'
        invariant
            0 <= lx <= gcc - gh,
            row_len == ly_row@.len(),
            row_len == m,
            ly_row@ =~= sg[ly as int],
            ly == gcr - gh,
            sg == grid_view(grid),
            valid_grid(n as int, m as int, sg),
            is_black_square_centered_at(n as int, m as int, sg, gcr, gcc, gh),
            0 <= gcr < n as int,
            0 <= gcc < m as int,
            gh >= 0,
            0 <= ly < n,
            m < 0x4000_0000i64,
        decreases gcc - gh - lx,
    {
        proof {
            assert(cell_in_square(ly as int, gcc - gh, gcr, gcc, gh));
            assert(sg[ly as int][gcc - gh] == 'B');
        }
        lx = lx + 1;
    }

    proof {
        if lx < gcc - gh {
            assert(!cell_in_square(ly as int, lx as int, gcr, gcc, gh));
            assert(sg[ly as int][lx as int] == 'W');
            // ly_row@[lx] == sg[ly][lx] == 'W', but loop exited with ly_row[lx] == 'B' - contradiction
            assert(false);
        }
        assert(lx == gcc - gh);
    }

    // Loop 4: find first non-'B' column after lx
    let mut rx: i64 = lx + 1;
    while rx < row_len && ly_row[rx as usize] == 'B'
        invariant
            rx > gcc - gh,
            rx <= gcc + gh + 1,
            row_len == ly_row@.len(),
            row_len == m,
            ly_row@ =~= sg[ly as int],
            ly == gcr - gh,
            lx == gcc - gh,
            sg == grid_view(grid),
            valid_grid(n as int, m as int, sg),
            is_black_square_centered_at(n as int, m as int, sg, gcr, gcc, gh),
            0 <= gcr < n as int,
            0 <= gcc < m as int,
            gh >= 0,
            0 <= ly < n,
            m < 0x4000_0000i64,
        decreases gcc + gh + 1 - rx,
    {
        proof {
            if rx > gcc + gh {
                assert(!cell_in_square(ly as int, rx as int, gcr, gcc, gh));
                assert(sg[ly as int][rx as int] == 'W');
                // ly_row@[rx] == sg[ly][rx] == 'W', but loop condition has ly_row[rx] == 'B' - contradiction
                assert(false);
            }
        }
        rx = rx + 1;
    }

    proof {
        if rx <= gcc + gh {
            assert(cell_in_square(ly as int, rx as int, gcr, gcc, gh));
            assert(sg[ly as int][rx as int] == 'B');
            // ly_row@[rx] == sg[ly][rx] == 'B', but loop exited with ly_row[rx] != 'B' - contradiction
            assert(false);
        }
        assert(rx == gcc + gh + 1);
    }

    // Compute center
    let y = (ly + ry) / 2;
    let x = (lx + rx) / 2;
    let r = y + 1;
    let c = x + 1;

    proof {
        assert(ly + ry == 2 * gcr + 1) by(nonlinear_arith)
            requires ly == gcr - gh, ry == gcr + gh + 1;
        assert(y == gcr);
        assert(lx + rx == 2 * gcc + 1) by(nonlinear_arith)
            requires lx == gcc - gh, rx == gcc + gh + 1;
        assert(x == gcc);
        assert(r - 1 == gcr);
        assert(c - 1 == gcc);
        assert(1 <= r <= n);
        assert(1 <= c <= m);
        assert(is_black_square_centered_at(n as int, m as int, sg, (r - 1) as int, (c - 1) as int, gh));
        prove_exists_h(n as int, m as int, sg, (r - 1) as int, (c - 1) as int, gh);
    }

    (r, c)
}

fn main() {}

} // verus!

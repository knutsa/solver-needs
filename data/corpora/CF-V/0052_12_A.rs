use vstd::prelude::*;

verus! {

spec fn valid_grid(grid: Seq<Seq<char>>) -> bool {
    grid.len() == 3 && forall|i: int| #![trigger grid[i]] 0 <= i < 3 ==> grid[i].len() == 3
}

spec fn symmetric_about_center(grid: Seq<Seq<char>>) -> bool
    recommends valid_grid(grid)
{
    forall|i: int, j: int| #![trigger grid[i][j]] (0 <= i < 3 && 0 <= j < 3) ==>
        (grid[i][j] == 'X' ==> grid[2 - i][2 - j] == 'X')
}

spec fn checked_so_far(grid: Seq<Seq<char>>, row: int, col: int) -> bool
    recommends
        valid_grid(grid),
        0 <= row,
        row <= 3,
        0 <= col,
        col <= 3
{
    forall|i: int, j: int| #![trigger grid[i][j]] (0 <= i < row && 0 <= j < 3) ==>
        (grid[i][j] == 'X' ==> grid[2 - i][2 - j] == 'X')
}

spec fn checked_row(grid: Seq<Seq<char>>, row: int, col: int) -> bool
    recommends
        valid_grid(grid),
        0 <= row,
        row < 3,
        0 <= col,
        col <= 3
{
    forall|j: int| #![trigger grid[row][j]] (0 <= j < col) ==>
        (grid[row][j] == 'X' ==> grid[2 - row][2 - j] == 'X')
}

#[verifier::loop_isolation(false)]
fn super_agent(grid: &Vec<Vec<char>>) -> (symmetric: bool)
    requires
        valid_grid(grid@.map_values(|row: Vec<char>| row@)),
    ensures
        symmetric == symmetric_about_center(grid@.map_values(|row: Vec<char>| row@)),
{
    let ghost g = grid@.map_values(|row: Vec<char>| row@);
    let mut bad = false;
    let mut i: usize = 0;
    while i < 3
        invariant
            0 <= i <= 3,
            valid_grid(g),
            g == grid@.map_values(|row: Vec<char>| row@),
            !bad == checked_so_far(g, i as int, 0),
        decreases 3 - i,
    {
        let mut j: usize = 0;
        while j < 3
            invariant
                0 <= i < 3,
                0 <= j <= 3,
                valid_grid(g),
                g == grid@.map_values(|row: Vec<char>| row@),
                !bad == (checked_so_far(g, i as int, 0) && checked_row(g, i as int, j as int)),
            decreases 3 - j,
        {
            assert(g[i as int].len() == 3);
            assert(g[2 - i as int].len() == 3);
            if grid[i][j] == 'X' && grid[2 - i][2 - j] != 'X' {
                bad = true;
            }
            j = j + 1;
        }
        i = i + 1;
    }
    !bad
}

fn main() {}

} // verus!
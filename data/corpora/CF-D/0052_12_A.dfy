ghost predicate ValidGrid(grid: seq<seq<char>>)
{
  |grid| == 3 && forall i :: 0 <= i < 3 ==> |grid[i]| == 3
}

// A grid of pressed keys is symmetric about the center iff
// every pressed key's 180°-rotated counterpart is also pressed.
ghost predicate SymmetricAboutCenter(grid: seq<seq<char>>)
  requires ValidGrid(grid)
{
  forall i, j :: (0 <= i < 3 && 0 <= j < 3) ==>
    (grid[i][j] == 'X' ==> grid[2 - i][2 - j] == 'X')
}

ghost predicate CheckedSoFar(grid: seq<seq<char>>, row: int, col: int)
  requires ValidGrid(grid)
  requires 0 <= row <= 3
  requires 0 <= col <= 3
{
  forall i, j :: (0 <= i < row && 0 <= j < 3) ==>
    (grid[i][j] == 'X' ==> grid[2 - i][2 - j] == 'X')
}

ghost predicate CheckedRow(grid: seq<seq<char>>, row: int, col: int)
  requires ValidGrid(grid)
  requires 0 <= row < 3
  requires 0 <= col <= 3
{
  forall j :: (0 <= j < col) ==>
    (grid[row][j] == 'X' ==> grid[2 - row][2 - j] == 'X')
}

method SuperAgent(grid: seq<seq<char>>) returns (symmetric: bool)
  requires ValidGrid(grid)
  ensures symmetric == SymmetricAboutCenter(grid)
{
  var bad := false;
  var i := 0;
  while i < 3
    invariant 0 <= i <= 3
    invariant !bad == CheckedSoFar(grid, i, 0)
  {
    var j := 0;
    while j < 3
      invariant 0 <= j <= 3
      invariant !bad == (CheckedSoFar(grid, i, 0) && CheckedRow(grid, i, j))
    {
      if grid[i][j] == 'X' && grid[2 - i][2 - j] != 'X' {
        bad := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  symmetric := !bad;
}

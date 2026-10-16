ghost predicate ValidGrid(n: int, m: int, grid: seq<string>)
{
  n > 0 && m > 0 && |grid| == n &&
  (forall i | 0 <= i < n :: |grid[i]| == m) &&
  (forall i | 0 <= i < n :: forall j | 0 <= j < m ::
    grid[i][j] == 'W' || grid[i][j] == 'B')
}

// A cell (i,j) lies inside the axis-aligned square with given center and half-side-length
ghost predicate CellInSquare(i: int, j: int, centerRow: int, centerCol: int, half: int)
{
  centerRow - half <= i <= centerRow + half &&
  centerCol - half <= j <= centerCol + half
}

// The grid consists of exactly one black square of side length 2*half+1 (odd)
// centered at (centerRow, centerCol) in 0-indexed coordinates, with all other cells white
ghost predicate IsBlackSquareCenteredAt(n: int, m: int, grid: seq<string>,
                                   centerRow: int, centerCol: int, half: int)
  requires |grid| == n && n > 0 && m > 0
  requires forall i | 0 <= i < n :: |grid[i]| == m
{
  half >= 0 &&
  centerRow - half >= 0 && centerRow + half < n &&
  centerCol - half >= 0 && centerCol + half < m &&
  (forall i | 0 <= i < n ::
    forall j | 0 <= j < m ::
      if CellInSquare(i, j, centerRow, centerCol, half)
      then grid[i][j] == 'B'
      else grid[i][j] == 'W')
}

// There exists some black square painted on the grid
ghost predicate HasBlackSquare(n: int, m: int, grid: seq<string>)
  requires |grid| == n && n > 0 && m > 0
  requires forall i | 0 <= i < n :: |grid[i]| == m
{
  exists cr | 0 <= cr < n ::
    exists cc | 0 <= cc < m ::
      exists h: nat ::
        IsBlackSquareCenteredAt(n, m, grid, cr, cc, h)
}

lemma RowOutsideHasNoBlack(n: int, m: int, grid: seq<string>, cr: int, cc: int, half: int, i: int)
  requires |grid| == n && n > 0 && m > 0
  requires forall ii | 0 <= ii < n :: |grid[ii]| == m
  requires IsBlackSquareCenteredAt(n, m, grid, cr, cc, half)
  requires 0 <= i < n
  requires i < cr - half || i > cr + half
  ensures 'B' !in grid[i]
{
  forall j | 0 <= j < |grid[i]|
    ensures grid[i][j] != 'B'
  {
    assert !CellInSquare(i, j, cr, cc, half);
  }
}

lemma RowInsideHasBlack(n: int, m: int, grid: seq<string>, cr: int, cc: int, half: int, i: int)
  requires |grid| == n && n > 0 && m > 0
  requires forall ii | 0 <= ii < n :: |grid[ii]| == m
  requires IsBlackSquareCenteredAt(n, m, grid, cr, cc, half)
  requires 0 <= i < n
  requires cr - half <= i <= cr + half
  ensures 'B' in grid[i]
{
  assert CellInSquare(i, cc, cr, cc, half);
  assert 0 <= cc < |grid[i]|;
  assert grid[i][cc] == 'B';
}

// Internal method with ghost out parameter (avoids existential in postcondition)
method FindSquareInternal(n: int, m: int, grid: seq<string>) returns (r: int, c: int, ghost h: nat)
  requires ValidGrid(n, m, grid)
  requires HasBlackSquare(n, m, grid)
  ensures 1 <= r <= n && 1 <= c <= m
  ensures IsBlackSquareCenteredAt(n, m, grid, r - 1, c - 1, h)
{
  // Extract ghost witnesses from HasBlackSquare
  ghost var gcr: int :| 0 <= gcr < n &&
    (exists cc | 0 <= cc < m :: exists h: nat ::
      IsBlackSquareCenteredAt(n, m, grid, gcr, cc, h));
  ghost var gcc: int :| 0 <= gcc < m &&
    (exists hh: nat :: IsBlackSquareCenteredAt(n, m, grid, gcr, gcc, hh));
  ghost var ghalf: nat :| IsBlackSquareCenteredAt(n, m, grid, gcr, gcc, ghalf);

  // Loop 1: find first row with 'B'
  var ly := 0;
  while ly < |grid| && 'B' !in grid[ly]
    invariant 0 <= ly <= gcr - ghalf
    decreases gcr - ghalf - ly
  {
    RowInsideHasBlack(n, m, grid, gcr, gcc, ghalf, gcr - ghalf);
    ly := ly + 1;
  }
  if ly < gcr - ghalf {
    RowOutsideHasNoBlack(n, m, grid, gcr, gcc, ghalf, ly);
    assert false;
  }
  assert ly == gcr - ghalf;

  // Loop 2: find first row after ly without 'B'
  var ry := ly + 1;
  while ry < |grid| && 'B' in grid[ry]
    invariant gcr - ghalf < ry <= gcr + ghalf + 1
    decreases gcr + ghalf + 1 - ry
  {
    if ry > gcr + ghalf {
      RowOutsideHasNoBlack(n, m, grid, gcr, gcc, ghalf, ry);
      assert false;
    }
    ry := ry + 1;
  }
  if ry <= gcr + ghalf {
    RowInsideHasBlack(n, m, grid, gcr, gcc, ghalf, ry);
    assert false;
  }
  assert ry == gcr + ghalf + 1;

  // Loop 3: find first 'B' column in row ly
  var lx := 0;
  while lx < |grid[ly]| && grid[ly][lx] != 'B'
    invariant 0 <= lx <= gcc - ghalf
    decreases gcc - ghalf - lx
  {
    assert CellInSquare(ly, gcc - ghalf, gcr, gcc, ghalf);
    assert grid[ly][gcc - ghalf] == 'B';
    lx := lx + 1;
  }
  if lx < gcc - ghalf {
    assert !CellInSquare(ly, lx, gcr, gcc, ghalf);
    assert grid[ly][lx] == 'W';
    assert false;
  }
  assert lx == gcc - ghalf;

  // Loop 4: find first non-'B' column after lx
  var rx := lx + 1;
  while rx < |grid[ly]| && grid[ly][rx] == 'B'
    invariant gcc - ghalf < rx <= gcc + ghalf + 1
    decreases gcc + ghalf + 1 - rx
  {
    if rx > gcc + ghalf {
      assert !CellInSquare(ly, rx, gcr, gcc, ghalf);
      assert grid[ly][rx] == 'W';
      assert false;
    }
    rx := rx + 1;
  }
  if rx <= gcc + ghalf {
    assert CellInSquare(ly, rx, gcr, gcc, ghalf);
    assert grid[ly][rx] == 'B';
    assert false;
  }
  assert rx == gcc + ghalf + 1;

  // Compute center
  var y := (ly + ry) / 2;
  var x := (lx + rx) / 2;
  r := y + 1;
  c := x + 1;
  h := ghalf;

  assert ly + ry == 2 * gcr + 1;
  assert y == gcr;
  assert lx + rx == 2 * gcc + 1;
  assert x == gcc;
  assert r - 1 == gcr;
  assert c - 1 == gcc;
  assert 1 <= r <= n;
  assert 1 <= c <= m;
  assert IsBlackSquareCenteredAt(n, m, grid, r - 1, c - 1, ghalf);
}

method FindSquare(n: int, m: int, grid: seq<string>) returns (r: int, c: int)
  requires ValidGrid(n, m, grid)
  requires HasBlackSquare(n, m, grid)
  ensures 1 <= r <= n && 1 <= c <= m
  ensures exists h: nat ::
            IsBlackSquareCenteredAt(n, m, grid, r - 1, c - 1, h)
{
  ghost var h: nat;
  r, c, h := FindSquareInternal(n, m, grid);
  assert IsBlackSquareCenteredAt(n, m, grid, r - 1, c - 1, h);
}

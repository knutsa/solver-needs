// The grid has uniform row width (a rectangular sheet)
ghost predicate Rectangular(grid: seq<string>)
{
  |grid| > 0 &&
  forall i | 0 <= i < |grid| :: |grid[i]| == |grid[0]|
}

// The grid contains at least one shaded cell ('*')
ghost predicate HasStar(grid: seq<string>)
{
  exists r | 0 <= r < |grid| ::
    exists c | 0 <= c < |grid[r]| ::
      grid[r][c] == '*'
}

// The result is the sub-rectangle of grid spanning rows [top..bottom) and columns [left..right)
ghost predicate IsSubRectangle(grid: seq<string>, result: seq<string>,
                               top: int, bottom: int, left: int, right: int)
{
  0 <= top < bottom <= |grid| &&
  0 <= left < right &&
  (forall r | top <= r < bottom :: right <= |grid[r]|) &&
  |result| == bottom - top &&
  (forall i | 0 <= i < bottom - top :: result[i] == grid[top + i][left..right])
}

// Every shaded cell in the entire grid lies within the rectangle [top..bottom) x [left..right)
ghost predicate ContainsAllShaded(grid: seq<string>,
                                  top: int, bottom: int, left: int, right: int)
{
  forall r | 0 <= r < |grid| ::
    forall c | 0 <= c < |grid[r]| ::
      grid[r][c] == '*' ==> (top <= r < bottom && left <= c < right)
}

// The rectangle is tight: each of its four edges touches at least one shaded cell.
// For axis-aligned rectangles, this is equivalent to having minimum area among all
// rectangles that contain every shaded cell.
ghost predicate TightBounds(grid: seq<string>,
                            top: int, bottom: int, left: int, right: int)
{
  0 <= top < bottom <= |grid| &&
  0 <= left < right &&
  (forall r | top <= r < bottom :: right <= |grid[r]|) &&
  // Top edge touches a shaded cell
  (exists c | left <= c < right :: grid[top][c] == '*') &&
  // Bottom edge touches a shaded cell
  (exists c {:trigger grid[bottom - 1][c]} | left <= c < right :: grid[bottom - 1][c] == '*') &&
  // Left edge touches a shaded cell
  (exists r | top <= r < bottom :: grid[r][left] == '*') &&
  // Right edge touches a shaded cell
  (exists r | top <= r < bottom :: grid[r][right - 1] == '*')
}

// The result is the minimum-cost rectangle cut from the grid containing all shaded cells
ghost predicate IsMinimalBoundingBox(grid: seq<string>, result: seq<string>,
                                     top: int, bottom: int, left: int, right: int)
{
  IsSubRectangle(grid, result, top, bottom, left, right) &&
  ContainsAllShaded(grid, top, bottom, left, right) &&
  TightBounds(grid, top, bottom, left, right)
}

method Letter(grid: seq<string>) returns (result: seq<string>)
  decreases *
  requires Rectangular(grid)
  requires HasStar(grid)
  ensures exists  top, bottom, left, right {:trigger IsMinimalBoundingBox(grid, result, top, bottom, left, right)} |
            0 <= top < |grid| && 0 <= bottom <= |grid| && 0 <= left < |grid[0]| && 0 <= right <= |grid[0]| ::
            IsMinimalBoundingBox(grid, result, top, bottom, left, right)
{
  var n := |grid|;
  var m := |grid[0]|;

  // === FIND TOP: first row containing a '*' ===
  var top := 0;
  var topDone := false;
  while top < n && !topDone
    invariant 0 <= top <= n
    invariant forall r, c | 0 <= r < top && 0 <= c < |grid[r]| :: grid[r][c] != '*'
    invariant topDone ==> top < n
    invariant topDone ==> exists c | 0 <= c < |grid[top]| :: grid[top][c] == '*'
    decreases n - top, !topDone
  {
    // assert |grid[top]| == m;
    var j := 0;
    var jDone := false;
    while j < m && !jDone
      invariant 0 <= j <= m
      invariant !jDone ==> forall c | 0 <= c < j :: grid[top][c] != '*'
      invariant jDone ==> 0 <= j < m && grid[top][j] == '*'
      decreases m - j, !jDone
    {
      if grid[top][j] == '*' {
        jDone := true;
      } else {
        j := j + 1;
      }
    }
    if jDone {
      topDone := true;
    } else {
      // assert forall c | 0 <= c < |grid[top]| :: grid[top][c] != '*';
      top := top + 1;
    }
  }
  if !topDone {
    // assert forall r | 0 <= r < |grid| :: forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*';
    // assert !HasStar(grid);
    // assert false;
    result := []; return;
  }

  // === FIND BOTTOM: last row containing a '*' ===
  var bot := n - 1;
  var botDone := false;
  while bot >= 0 && !botDone
    invariant -1 <= bot <= n - 1
    invariant !botDone ==> forall r | bot < r < n :: forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*'
    invariant botDone ==> 0 <= bot < n
    invariant botDone ==> exists c | 0 <= c < |grid[bot]| :: grid[bot][c] == '*'
    invariant botDone ==> forall r | bot < r < n :: forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*'
    decreases bot + 1, !botDone
  {
    // assert |grid[bot]| == m;
    var j := 0;
    var jDone := false;
    while j < m && !jDone
      invariant 0 <= j <= m
      invariant !jDone ==> forall c | 0 <= c < j :: grid[bot][c] != '*'
      invariant jDone ==> 0 <= j < m && grid[bot][j] == '*'
      decreases m - j, !jDone
    {
      if grid[bot][j] == '*' {
        jDone := true;
      } else {
        j := j + 1;
      }
    }
    if jDone {
      botDone := true;
    } else {
      // assert forall c | 0 <= c < |grid[bot]| :: grid[bot][c] != '*';
      bot := bot - 1;
    }
  }
  if !botDone {
    // assert forall r | 0 <= r < n :: forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*';
    // assert false;
    result := []; return;
  }
  var bottom := bot + 1;

  // top <= bot because row top has a star but rows > bot don't
  if top > bot {
    // assert forall c | 0 <= c < |grid[top]| :: grid[top][c] != '*';
    // assert false;
  }

  // === FIND LEFT: first column containing a '*' ===
  var left := 0;
  var leftDone := false;
  while left < m && !leftDone
    invariant 0 <= left <= m
    invariant !leftDone ==> forall r | 0 <= r < n :: forall c | 0 <= c < left :: grid[r][c] != '*'
    invariant leftDone ==> 0 <= left < m
    invariant leftDone ==> exists r | 0 <= r < n :: grid[r][left] == '*'
    invariant leftDone ==> forall r | 0 <= r < n :: forall c | 0 <= c < left :: grid[r][c] != '*'
    decreases m - left, !leftDone
  {
    var r := 0;
    var rDone := false;
    while r < n && !rDone
      invariant 0 <= r <= n
      invariant !rDone ==> forall rr | 0 <= rr < r :: grid[rr][left] != '*'
      invariant rDone ==> 0 <= r < n && grid[r][left] == '*'
      decreases n - r, !rDone
    {
      if grid[r][left] == '*' {
        rDone := true;
      } else {
        r := r + 1;
      }
    }
    if rDone {
      leftDone := true;
    } else {
      // assert forall rr | 0 <= rr < n :: grid[rr][left] != '*';
      left := left + 1;
    }
  }
  if !leftDone {
    // forall r | 0 <= r < n
    //   ensures forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*'
    // {
    //   // assert |grid[r]| == m;
    // }
    // assert false;
    result := []; return;
  }

  // === FIND RIGHT: last column containing a '*' ===
  var ri := m - 1;
  var rightDone := false;
  while ri >= 0 && !rightDone
    invariant -1 <= ri <= m - 1
    invariant !rightDone ==> forall r | 0 <= r < n :: forall c | ri < c < m :: grid[r][c] != '*'
    invariant rightDone ==> 0 <= ri < m
    invariant rightDone ==> exists r | 0 <= r < n :: grid[r][ri] == '*'
    invariant rightDone ==> forall r | 0 <= r < n :: forall c | ri < c < m :: grid[r][c] != '*'
    decreases ri + 1, !rightDone
  {
    var r := 0;
    var rDone := false;
    while r < n && !rDone
      invariant 0 <= r <= n
      invariant !rDone ==> forall rr | 0 <= rr < r :: grid[rr][ri] != '*'
      invariant rDone ==> 0 <= r < n && grid[r][ri] == '*'
      decreases n - r, !rDone
    {
      if grid[r][ri] == '*' {
        rDone := true;
      } else {
        r := r + 1;
      }
    }
    if rDone {
      rightDone := true;
    } else {
      // assert forall rr | 0 <= rr < n :: grid[rr][ri] != '*';
      ri := ri - 1;
    }
  }
  if !rightDone {
    // forall r | 0 <= r < n
    //   ensures forall c | 0 <= c < |grid[r]| :: grid[r][c] != '*'
    // {
    //   // assert |grid[r]| == m;
    // }
    // assert false;
    result := []; return;
  }
  var right := ri + 1;

  // left <= ri because column left has a star but columns > ri don't
  if left > ri {
    var r0 :| 0 <= r0 < n && grid[r0][left] == '*';
    // assert ri < left < m;
    // assert grid[r0][left] != '*';
    // assert false;
  }

  // === PROVE CONTAINSALLSHADED ===
  // assert ContainsAllShaded(grid, top, bottom, left, right) by {
  //   forall r | 0 <= r < |grid|
  //     ensures forall c | 0 <= c < |grid[r]| ::
  //               grid[r][c] == '*' ==> (top <= r < bottom && left <= c < right)
  //   {
  //     assert |grid[r]| == m;
  //     forall c | 0 <= c < |grid[r]|
  //       ensures grid[r][c] == '*' ==> (top <= r < bottom && left <= c < right)
  //     {
  //       if grid[r][c] == '*' {
  //         if r < top { assert false; }
  //         if r >= bottom { assert r > bot; assert false; }
  //         if c < left { assert false; }
  //         if c >= right { assert c > ri; assert c < m; assert false; }
  //       }
  //     }
  //   }
  // }

  // === PROVE TIGHTBOUNDS ===
  // assert exists c | 0 <= c < |grid[top]| :: grid[top][c] == '*';
  // assert exists c | 0 <= c < |grid[bot]| :: grid[bot][c] == '*';
  // assert exists r | 0 <= r < n :: grid[r][left] == '*';
  // assert exists r | 0 <= r < n :: grid[r][ri] == '*';

  // assert exists c | left <= c < right :: grid[top][c] == '*' by {
  //   var c0 :| 0 <= c0 < |grid[top]| && grid[top][c0] == '*';
  //   assert left <= c0 < right;
  // }
  // assert exists c {:trigger grid[bot][c]} | left <= c < right :: grid[bottom - 1][c] == '*';
  assert exists c {:trigger grid[bottom - 1][c]} | left <= c < right :: grid[bottom - 1][c] == '*' by {
    var c0 :| 0 <= c0 < |grid[bot]| && grid[bottom - 1][c0] == '*';
    // assert left <= c0 < right;
  }
  // assert exists r | top <= r < bottom :: grid[r][left] == '*' by {
  //   var r0 :| 0 <= r0 < n && grid[r0][left] == '*';
  //   assert top <= r0 < bottom;
  // }
  // assert exists r | top <= r < bottom :: grid[r][right - 1] == '*' by {
  //   var r0 :| 0 <= r0 < n && grid[r0][ri] == '*';
  //   assert top <= r0 < bottom;
  // }

  // assert forall r | top <= r < bottom :: right <= |grid[r]| by {
  //   forall r | top <= r < bottom ensures right <= |grid[r]| {
  //     assert |grid[r]| == m;
  //   }
  // }

  // assert TightBounds(grid, top, bottom, left, right);

  // === EXTRACT SUB-RECTANGLE ===
  result := [];
  var idx := top;
  while idx < bottom
    invariant top <= idx <= bottom
    invariant |result| == idx - top
    invariant forall k | 0 <= k < idx - top :: result[k] == grid[top + k][left..right]
    decreases bottom - idx
  {
    // assert |grid[idx]| == m;
    result := result + [grid[idx][left..right]];
    idx := idx + 1;
  }

  // === PROVE POSTCONDITION ===
  // assert IsSubRectangle(grid, result, top, bottom, left, right);
  assert IsMinimalBoundingBox(grid, result, top, bottom, left, right); // Essential
  // assert 0 <= top < |grid|;
  // assert 0 <= bottom <= |grid|;
  // assert 0 <= left < |grid[0]|;
  // assert 0 <= right <= |grid[0]|;
}

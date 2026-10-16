// ─────────────── Arithmetic helpers ───────────────

ghost function Abs(x: int): int {
  if x >= 0 then x else -x
}

ghost function Max(x: int, y: int): int {
  if x >= y then x else y
}

ghost function Min(x: int, y: int): int {
  if x <= y then x else y
}

// ─────────────── Sorting three values ───────────────

ghost function Min3(a: int, b: int, c: int): int {
  Min(a, Min(b, c))
}

ghost function Max3(a: int, b: int, c: int): int {
  Max(a, Max(b, c))
}

ghost function Mid3(a: int, b: int, c: int): int {
  a + b + c - Min3(a, b, c) - Max3(a, b, c)
}

// ─────────────── Problem-level predicates ───────────────

// A configuration of three walkers is valid iff every pair
// is separated by at least d.
ghost predicate AllPairsSeparated(p: int, q: int, r: int, d: int) {
  Abs(p - q) >= d && Abs(p - r) >= d && Abs(q - r) >= d
}

// Total unit moves for walkers to go from (a,b,c) to (a',b',c').
ghost function TotalMoves(a: int, b: int, c: int, a': int, b': int, c': int): int {
  Abs(a - a') + Abs(b - b') + Abs(c - c')
}

// ─────────────── Witness: optimal final positions ───────────────

// Keep the median walker fixed; push the lowest down and the
// highest up just enough to open gaps of at least d.
ghost function OptimalLo(a: int, b: int, c: int, d: int): int {
  Min(Min3(a, b, c), Mid3(a, b, c) - d)
}

ghost function OptimalMid(a: int, b: int, c: int, d: int): int {
  Mid3(a, b, c)
}

ghost function OptimalHi(a: int, b: int, c: int, d: int): int {
  Max(Max3(a, b, c), Mid3(a, b, c) + d)
}

// ─────────────── Minimum moves ───────────────

// The minimum total displacement is the sum of the gap deficits
// between consecutive sorted positions.
ghost function MinimumMoves(a: int, b: int, c: int, d: int): int {
  Max(0, d - (Mid3(a, b, c) - Min3(a, b, c)))
  + Max(0, d - (Max3(a, b, c) - Mid3(a, b, c)))
}

// ═══════════════════════════════════════════════════════

method Ropewalkers(a: int, b: int, c: int, d: int) returns (result: int)
  // The result equals the minimum total displacement
  ensures result == MinimumMoves(a, b, c, d)
  // The result is non-negative
  ensures result >= 0
  // Feasibility: the optimal final positions satisfy the separation constraint
  ensures AllPairsSeparated(OptimalLo(a, b, c, d), OptimalMid(a, b, c, d), OptimalHi(a, b, c, d), d)
  // The cost of reaching those optimal positions equals result
  ensures TotalMoves(Min3(a, b, c), Mid3(a, b, c), Max3(a, b, c),
                     OptimalLo(a, b, c, d), OptimalMid(a, b, c, d), OptimalHi(a, b, c, d)) == result
{
  var x := a;
  var y := b;
  var z := c;

  if x > y {
    var tmp := x;
    x := y;
    y := tmp;
  }
  if y > z {
    var tmp := y;
    y := z;
    z := tmp;
  }
  if x > y {
    var tmp := x;
    x := y;
    y := tmp;
  }

  // After sorting network: x <= y <= z
  assert x <= y <= z;
  assert x == Min3(a, b, c);
  assert y == Mid3(a, b, c);
  assert z == Max3(a, b, c);

  var val1 := d - (y - x);
  var val2 := d - (z - y);
  if val1 < 0 { val1 := 0; }
  if val2 < 0 { val2 := 0; }

  result := val1 + val2;
}

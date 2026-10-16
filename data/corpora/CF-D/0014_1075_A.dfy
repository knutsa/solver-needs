// ── Helper functions ──

ghost function Abs(x: int): int
{ if x >= 0 then x else -x }

ghost function Max(a: int, b: int): int
{ if a >= b then a else b }

// ── Problem formalization ──

// Chebyshev (L∞) distance between two cells
ghost function ChebyshevDist(r1: int, c1: int, r2: int, c2: int): int
{ Max(Abs(r1 - r2), Abs(c1 - c2)) }

// A valid single king move: to an adjacent cell (8 directions) within an n×n board
ghost predicate ValidKingStep(r1: int, c1: int, r2: int, c2: int, n: int)
{
  1 <= r1 <= n && 1 <= c1 <= n &&
  1 <= r2 <= n && 1 <= c2 <= n &&
  Abs(r1 - r2) <= 1 && Abs(c1 - c2) <= 1 &&
  (r1 != r2 || c1 != c2)
}

// Greedy one step toward (tr, tc): move each coordinate ±1 in the correct direction
ghost function StepToward(r: int, c: int, tr: int, tc: int): (int, int)
{
  (r + (if tr > r then 1 else if tr < r then -1 else 0),
   c + (if tc > c then 1 else if tc < c then -1 else 0))
}

// EXISTENCE witness: the greedy step is a valid king move that reduces the
// Chebyshev distance by exactly 1. Repeated application (induction on distance)
// constructs a valid king path of length ChebyshevDist.
ghost predicate GreedyStepValid(r: int, c: int, tr: int, tc: int, n: int)
{
  1 <= r <= n && 1 <= c <= n && 1 <= tr <= n && 1 <= tc <= n &&
  ((r == tr && c == tc)
   ||
   (var p := StepToward(r, c, tr, tc);
    ValidKingStep(r, c, p.0, p.1, n) &&
    ChebyshevDist(p.0, p.1, tr, tc) == ChebyshevDist(r, c, tr, tc) - 1))
}

// OPTIMALITY: no single king step can reduce Chebyshev distance by more than 1.
// By induction on path length, any path of k steps reduces distance by at most k,
// so the minimum number of moves from (r,c) to (tr,tc) is at least ChebyshevDist.
ghost predicate NoStepReducesByMoreThanOne(r: int, c: int, tr: int, tc: int)
{
  forall dr | -1 <= dr <= 1 ::
    forall dc | -1 <= dc <= 1 ::
      ChebyshevDist(r + dr, c + dc, tr, tc) >= ChebyshevDist(r, c, tr, tc) - 1
}

// Turn structure: White takes turns 1, 3, 5, … ; Black takes turns 2, 4, 6, …
// A king needing d optimal moves arrives at global turn:
//   2d−1 if White (moves first), or 2d if Black (moves second).
// If d = 0 the king starts on the coin (arrival turn 0).
ghost function ArrivalTurn(dist: int, movesFirst: bool): int
{
  if dist == 0 then 0
  else if movesFirst then 2 * dist - 1
  else 2 * dist
}

// The correct winner is the king whose arrival turn is strictly earlier.
ghost predicate CorrectWinner(winner: string, n: int, x: int, y: int)
  requires n >= 2 && 1 <= x <= n && 1 <= y <= n
{
  var whiteDist := ChebyshevDist(1, 1, x, y);
  var blackDist := ChebyshevDist(n, n, x, y);
  var whiteTurn := ArrivalTurn(whiteDist, true);
  var blackTurn := ArrivalTurn(blackDist, false);
  (winner == "White" <==> whiteTurn <= blackTurn) &&
  (winner == "Black" <==> whiteTurn > blackTurn)
}

// ── Lemmas ──

lemma AbsTriangle(a: int, d: int)
  requires -1 <= d <= 1
  ensures Abs(a + d) >= Abs(a) - 1
{
}

lemma MaxMonotone(a: int, b: int, c: int, d: int)
  requires a >= c - 1
  requires b >= d - 1
  ensures Max(a, b) >= Max(c, d) - 1
{
}

lemma NoStepReducesSingle(r: int, c: int, tr: int, tc: int, dr: int, dc: int)
  requires -1 <= dr <= 1 && -1 <= dc <= 1
  ensures ChebyshevDist(r + dr, c + dc, tr, tc) >= ChebyshevDist(r, c, tr, tc) - 1
{
  var a := r - tr;
  var b := c - tc;
  AbsTriangle(a, dr);
  AbsTriangle(b, dc);
  assert r + dr - tr == a + dr;
  assert c + dc - tc == b + dc;
  MaxMonotone(Abs(a + dr), Abs(b + dc), Abs(a), Abs(b));
}

lemma NoStepReducesLemma(r: int, c: int, tr: int, tc: int)
  ensures NoStepReducesByMoreThanOne(r, c, tr, tc)
{
  NoStepReducesSingle(r, c, tr, tc, -1, -1);
  NoStepReducesSingle(r, c, tr, tc, -1, 0);
  NoStepReducesSingle(r, c, tr, tc, -1, 1);
  NoStepReducesSingle(r, c, tr, tc, 0, -1);
  NoStepReducesSingle(r, c, tr, tc, 0, 0);
  NoStepReducesSingle(r, c, tr, tc, 0, 1);
  NoStepReducesSingle(r, c, tr, tc, 1, -1);
  NoStepReducesSingle(r, c, tr, tc, 1, 0);
  NoStepReducesSingle(r, c, tr, tc, 1, 1);
}

lemma GreedyStepValidLemma(r: int, c: int, tr: int, tc: int, n: int)
  requires 1 <= r <= n && 1 <= c <= n && 1 <= tr <= n && 1 <= tc <= n
  ensures GreedyStepValid(r, c, tr, tc, n)
{
  if r != tr || c != tc {
    var p := StepToward(r, c, tr, tc);
    assert 1 <= p.0 <= n;
    assert 1 <= p.1 <= n;
  }
}

// ── Method with specification ──

method KingsRace(n: int, x: int, y: int) returns (winner: string)
  requires n >= 2 && 1 <= x <= n && 1 <= y <= n
  ensures CorrectWinner(winner, n, x, y)
  ensures GreedyStepValid(1, 1, x, y, n)
  ensures GreedyStepValid(n, n, x, y, n)
  ensures NoStepReducesByMoreThanOne(1, 1, x, y)
  ensures NoStepReducesByMoreThanOne(n, n, x, y)
{
  var dx1 := if x - 1 >= 0 then x - 1 else 1 - x;
  var dy1 := if y - 1 >= 0 then y - 1 else 1 - y;
  var dist1 := if dx1 >= dy1 then dx1 else dy1;

  var dx2 := if x - n >= 0 then x - n else n - x;
  var dy2 := if y - n >= 0 then y - n else n - y;
  var dist2 := if dx2 >= dy2 then dx2 else dy2;

  assert dist1 == ChebyshevDist(1, 1, x, y);
  assert dist2 == ChebyshevDist(n, n, x, y);

  GreedyStepValidLemma(1, 1, x, y, n);
  GreedyStepValidLemma(n, n, x, y, n);
  NoStepReducesLemma(1, 1, x, y);
  NoStepReducesLemma(n, n, x, y);

  if dist1 <= dist2 {
    winner := "White";
  } else {
    winner := "Black";
  }
}

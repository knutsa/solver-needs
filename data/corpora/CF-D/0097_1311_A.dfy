// A single legal move: add a positive odd integer, or subtract a positive even integer.
ghost predicate ValidStep(from: int, to: int) {
  // Add positive odd: to = from + x, x >= 1, x odd
  (to > from && (to - from) % 2 == 1)
  ||
  // Subtract positive even: to = from - y, y >= 2, y even
  (from - to >= 2 && (from - to) % 2 == 0)
}

// Can we transform a into b using exactly `steps` legal moves?
// Base cases handle 0 and 1 step directly.
// For steps >= 2, there exists some intermediate value c reachable
// in one valid step from a, with the remainder reachable from c.
ghost predicate ReachableIn(a: int, b: int, steps: nat)
  decreases steps
{
  if steps == 0 then
    a == b
  else if steps == 1 then
    ValidStep(a, b)
  else
    exists c :: ValidStep(a, c) && ReachableIn(c, b, steps - 1)
}

method AddOddOrSubtractEven(a: int, b: int) returns (moves: int)
  requires a >= 1 && b >= 1
  ensures 0 <= moves <= 2
  ensures ReachableIn(a, b, moves)
  ensures forall k | 0 <= k < moves :: !ReachableIn(a, b, k)
{
  if a == b {
    moves := 0;
  } else if a % 2 == b % 2 && a > b {
    moves := 1;
  } else if a % 2 != b % 2 && b > a {
    moves := 1;
  } else {
    moves := 2;
    // Witness: go via c = a + 1 (adding 1, a positive odd number)
    var c := a + 1;
    assert ValidStep(a, c);
    assert ValidStep(c, b);
    assert ReachableIn(c, b, 1);
    assert ReachableIn(a, b, 2);
  }
}

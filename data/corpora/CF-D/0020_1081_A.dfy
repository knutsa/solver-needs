// A valid game move: choose positive x < n that does not divide n
ghost predicate ValidMove(n: int, x: int)
{
  1 <= x < n && n % x != 0
}

// Can we reach target from start in at most `steps` valid moves?
ghost predicate Reachable(start: int, target: int, steps: nat)
  decreases steps
{
  start >= 1 && target >= 1 &&
  (start == target ||
   (steps > 0 &&
    exists x | 1 <= x < start :: ValidMove(start, x) && Reachable(start - x, target, steps - 1)))
}

// result is the minimum positive integer reachable from v via valid game moves
ghost predicate IsMinReachable(v: int, result: int)
{
  v >= 1 && result >= 1 &&
  Reachable(v, result, v) &&
  forall r :: 1 <= r < result ==> !Reachable(v, r, v)
}


method DefiniteGame(v: int) returns (result: int)
  requires v >= 1
  ensures IsMinReachable(v, result)
{
  if v == 2 {
    assert Reachable(2, 2, 2);
    assert !Reachable(2, 1, 2);
    return 2;
  } else if v == 1 {
    assert Reachable(1, 1, 1);
    return 1;
  } else {
    // v >= 3
    assert v >= 3;
    assert v == 1 * (v - 1) + 1;
    assert v % (v - 1) == 1;
    assert ValidMove(v, v - 1);
    assert Reachable(1, 1, v - 1);
    // Inlined from ReachableStep(v, 1, v - 1, v - 1)
    assert ValidMove((v), (v - 1)) && Reachable((v) - (v - 1), (1), ((v - 1) + 1) - 1);
    assert Reachable(v, 1, (v - 1) + 1);
    assert Reachable(v, 1, v);
    return 1;
  }
}

ghost predicate IsDivisibleAfterMoves(a: int, b: int, moves: int)
  requires b > 0
{
  moves >= 0 && (a + moves) % b == 0
}

ghost predicate IsMinimumMoves(a: int, b: int, moves: int)
  requires b > 0
{
  IsDivisibleAfterMoves(a, b, moves) &&
  forall m | 0 <= m < moves :: !IsDivisibleAfterMoves(a, b, m)
}

lemma {:induction false} AddBMod(x: nat, b: int)
  requires b > 0
  ensures (x + b) % b == x % b
  decreases x
{
  if x < b {
    // 0 <= x < b, so x % b == x
    // b <= x + b < 2*b, so (x + b) / b == 1, (x + b) % b == x
    assert (x + b) / b == 1;
  } else {
    // x >= b
    AddBMod(x - b, b);
    // IH: ((x - b) + b) % b == (x - b) % b
    // That is: x % b == (x - b) % b
    //
    // Also apply AddBMod to (x - b) to get:
    // (x - b + b) % b == (x - b) % b, done.
    //
    // But we need (x + b) % b == x % b.
    // (x + b) == ((x - b) + b) + b == (x - b) + 2*b
    // From IH: x % b == (x - b) % b
    // Apply AddBMod(x - b, b) again... wait, that's what IH gives.
    // We need (x + b) % b == x % b
    // Note: x + b >= 2b > b, so we can recurse on x + b - b = x... but that's circular.
    //
    // Different approach: from IH we know x % b == (x-b) % b for the SUB direction.
    // What we actually need is the ADD direction for arbitrary x.
    // Let's instead prove this by observing that x + b = (x - b) + 2b.
    // Need to show ((x-b) + 2b) % b == (x-b) % b.
    // We can call AddBMod(x - b, b) to get ((x-b)+b) % b == (x-b) % b.
    // Then AddBMod(x - b + b, b) = AddBMod(x, b)... which is what we're trying to prove. Circular.
    //
    // Actually wait, the decreases clause is on x. So AddBMod(x - b + b, b) = AddBMod(x, b)
    // has the same x, so we can't call it.
    //
    // Let me use a different decomposition.
    // x + b = (x - b) + b + b.
    // From IH: ((x - b) + b) % b == (x - b) % b → x % b == (x - b) % b
    // Need: (x + b) % b == x % b
    // Let y = x - b. Then x = y + b, x + b = y + 2b.
    // IH: (y + b) % b == y % b, i.e., x % b == y % b.
    // Need: (y + 2b) % b == (y + b) % b, i.e., (x + b) % b == x % b.
    // This is equivalent to AddBMod(y + b, b), but y + b = x, and decreases x doesn't decrease.
    // Stuck.

    // Let me try induction on x / b instead.
    assert false; // placeholder
  }
}

method DivisibilityProblem(a: int, b: int) returns (moves: int)
  requires a >= 1 && b >= 1
  ensures IsMinimumMoves(a, b, moves)
{
  moves := (b - a % b) % b;
}

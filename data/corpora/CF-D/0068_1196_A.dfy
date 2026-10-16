ghost function Min(x: int, y: int): int {
  if x <= y then x else y
}

// After Alice takes pile `ap`, Bob takes pile `bp`, and they split pile `sp`
// (Alice gets `s`, Bob gets `sp - s`), both equalize to the lesser total.
ghost function CandiesAfterDivision(ap: int, bp: int, sp: int, s: int): int
  requires 0 <= s <= sp
{
  Min(ap + s, bp + (sp - s))
}

// A valid division of piles (a, b, c) can achieve `result` candies for each person.
// There are three choices of which pile to split (the swap of Alice/Bob with the
// complementary split value yields the same min, so 3 cases cover all 6 permutations).
ghost predicate IsAchievable(a: int, b: int, c: int, result: int)
  requires a >= 0 && b >= 0 && c >= 0
{
  (exists s | 0 <= s <= c :: CandiesAfterDivision(a, b, c, s) == result)
  || (exists s | 0 <= s <= b :: CandiesAfterDivision(a, c, b, s) == result)
  || (exists s | 0 <= s <= a :: CandiesAfterDivision(b, c, a, s) == result)
}

// No valid division of piles (a, b, c) can yield more than `result` candies.
ghost predicate IsOptimal(a: int, b: int, c: int, result: int)
  requires a >= 0 && b >= 0 && c >= 0
{
  (forall s :: 0 <= s <= c ==> CandiesAfterDivision(a, b, c, s) <= result)
  && (forall s :: 0 <= s <= b ==> CandiesAfterDivision(a, c, b, s) <= result)
  && (forall s :: 0 <= s <= a ==> CandiesAfterDivision(b, c, a, s) <= result)
}

method ThreePilesOfCandies(a: int, b: int, c: int) returns (maxCandies: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures IsAchievable(a, b, c, maxCandies)
  ensures IsOptimal(a, b, c, maxCandies)
{
  maxCandies := (a + b + c) / 2;

  // Achievability: split the largest pile, witness s equalizes both sides
  if a >= b && a >= c {
    // Split pile a; Alice takes b, Bob takes c
    var s := maxCandies - b;
    assert 0 <= s <= a;
    assert CandiesAfterDivision(b, c, a, s) == maxCandies;
  } else if b >= a && b >= c {
    // Split pile b; Alice takes a, Bob takes c
    var s := maxCandies - a;
    assert 0 <= s <= b;
    assert CandiesAfterDivision(a, c, b, s) == maxCandies;
  } else {
    // Split pile c; Alice takes a, Bob takes b
    var s := maxCandies - a;
    assert 0 <= s <= c;
    assert CandiesAfterDivision(a, b, c, s) == maxCandies;
  }
}

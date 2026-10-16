// A good string consists of only 'a' and 'b' with every two consecutive letters distinct.
ghost predicate IsGoodString(s: seq<char>)
{
  (forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b') &&
  (forall i | 0 <= i < |s| - 1 :: s[i] != s[i+1])
}

// A good string with na 'a'-characters and nb 'b'-characters exists iff
// both counts are non-negative and they differ by at most 1.
ghost predicate GoodStringWithCounts(na: int, nb: int)
{
  na >= 0 && nb >= 0 && na - nb <= 1 && nb - na <= 1
}

// Whether a good string of exactly `len` characters can be formed by choosing
// some subset of the available pieces (at most a "a"s, b "b"s, c "ab"s)
// and concatenating them in some order.
//
// Selecting pa single-"a" pieces, pb single-"b" pieces, and pc "ab" pieces
// gives (pa + pc) total 'a'-characters and (pb + pc) total 'b'-characters,
// for a total length of pa + pb + 2*pc. A good string from these pieces
// exists iff the character counts differ by at most 1 — any such selection
// can be arranged into a valid good string.
ghost predicate AchievableLength(len: int, a: int, b: int, c: int)
{
  a >= 0 && b >= 0 && c >= 0 &&
  exists pa | 0 <= pa <= a ::
    exists pb | 0 <= pb <= b ::
      exists pc | 0 <= pc <= c ::
        GoodStringWithCounts(pa + pc, pb + pc) &&
        pa + pb + 2 * pc == len
}

lemma AchievableWitness(len: int, a: int, b: int, c: int, pa: int, pb: int, pc: int)
  requires a >= 0 && b >= 0 && c >= 0
  requires 0 <= pa <= a && 0 <= pb <= b && 0 <= pc <= c
  requires GoodStringWithCounts(pa + pc, pb + pc)
  requires pa + pb + 2 * pc == len
  ensures AchievableLength(len, a, b, c)
{
  assert GoodStringWithCounts(pa + pc, pb + pc) && pa + pb + 2 * pc == len;
}

lemma NotAchievable(n: int, a: int, b: int, c: int, maxLen: int)
  requires a >= 0 && b >= 0 && c >= 0
  requires n > maxLen
  requires if a == b then maxLen == 2 * a + 2 * c
           else if a > b then maxLen == 2 * b + 2 * c + 1
           else maxLen == 2 * a + 2 * c + 1
  ensures !AchievableLength(n, a, b, c)
{
}

method AnotherOneBitesTheDust(a: int, b: int, c: int) returns (maxLen: int)
  requires a >= 0 && b >= 0 && c >= 0
  ensures AchievableLength(maxLen, a, b, c)
  ensures forall n | maxLen < n <= a + b + 2 * c :: !AchievableLength(n, a, b, c)
{
  var x := a + c;
  var y := b + c;

  if x > y {
    x := y + 1;
  }
  if y > x {
    y := x + 1;
  }

  maxLen := x + y;

  // Prove achievability with explicit witnesses
  if a > b {
    AchievableWitness(maxLen, a, b, c, b + 1, b, c);
  } else if a < b {
    AchievableWitness(maxLen, a, b, c, a, a + 1, c);
  } else {
    AchievableWitness(maxLen, a, b, c, a, b, c);
  }

  // Prove optimality
  assert if a == b then maxLen == 2 * a + 2 * c
         else if a > b then maxLen == 2 * b + 2 * c + 1
         else maxLen == 2 * a + 2 * c + 1;

  forall n | maxLen < n <= a + b + 2 * c
    ensures !AchievableLength(n, a, b, c)
  {
    NotAchievable(n, a, b, c, maxLen);
  }
}

ghost function MaxOf(a: int, b: int): int {
  if a > b then a else b
}

ghost function MinOf(a: int, b: int): int {
  if a < b then a else b
}

// A valid solution: positive a, b, c whose pairwise maxima are exactly x, y, z
ghost predicate IsValidSolution(x: int, y: int, z: int, a: int, b: int, c: int) {
  a > 0 && b > 0 && c > 0 &&
  MaxOf(a, b) == x && MaxOf(a, c) == y && MaxOf(b, c) == z
}

// Does any valid solution exist?
ghost predicate SolutionExists(x: int, y: int, z: int)
  requires x > 0 && y > 0 && z > 0
{
  exists a ::
    exists b ::
      exists c ::
        IsValidSolution(x, y, z, a, b, c)
}

method ThreePairwiseMaximums(x: int, y: int, z: int) returns (possible: bool, a: int, b: int, c: int)
  requires x > 0 && y > 0 && z > 0
  ensures possible == SolutionExists(x, y, z)
  ensures possible ==> IsValidSolution(x, y, z, a, b, c)
{
  var m := x;
  if y > m { m := y; }
  if z > m { m := z; }

  var cnt := 0;
  if x == m { cnt := cnt + 1; }
  if y == m { cnt := cnt + 1; }
  if z == m { cnt := cnt + 1; }

  if cnt >= 2 {
    possible := true;
    a := if x <= y then x else y;
    b := if x <= z then x else z;
    c := if y <= z then y else z;
    assert IsValidSolution(x, y, z, a, b, c);
  } else {
    possible := false;
    a := 0;
    b := 0;
    c := 0;
    // cnt == 1: exactly one of x,y,z equals m = max(x,y,z)
    // Key insight: the largest of any a',b',c' appears in at least 2 pairwise maxima,
    // so the max of x,y,z must appear at least twice. Contradiction with cnt < 2.
    forall a': int, b': int, c': int
      ensures !IsValidSolution(x, y, z, a', b', c')
    {
      if a' > 0 && b' > 0 && c' > 0 && MaxOf(a', b') == x && MaxOf(a', c') == y && MaxOf(b', c') == z {
        if a' >= b' && a' >= c' {
          // a' is largest: MaxOf(a',b')=a'=x, MaxOf(a',c')=a'=y, so x==y
          // z = MaxOf(b',c') <= a' = x, so m = max(x,y,z) = x = y
          // Both x==m and y==m, so cnt >= 2, contradiction
          assert MaxOf(a', b') == a';
          assert MaxOf(a', c') == a';
          assert x == a' && y == a';
        } else if b' >= a' && b' >= c' {
          // b' is largest: MaxOf(a',b')=b'=x, MaxOf(b',c')=b'=z, so x==z
          assert MaxOf(a', b') == b';
          assert MaxOf(b', c') == b';
          assert x == b' && z == b';
        } else {
          // c' is largest: MaxOf(a',c')=c'=y, MaxOf(b',c')=c'=z, so y==z
          assert c' >= a' && c' >= b';
          assert MaxOf(a', c') == c';
          assert MaxOf(b', c') == c';
          assert y == c' && z == c';
        }
      }
    }
  }
}

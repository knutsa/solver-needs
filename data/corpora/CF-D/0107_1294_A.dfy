ghost predicate ValidDistribution(a: int, b: int, c: int, n: int, A: int, B: int, C: int)
{
  A >= 0 && B >= 0 && C >= 0
  && A + B + C == n
  && a + A == b + B
  && a + A == c + C
}

ghost predicate CanDistribute(a: int, b: int, c: int, n: int)
  requires n >= 0
{
  exists A: int, B: int, C: int
    :: ValidDistribution(a, b, c, n, A, B, C)
}

method CollectingCoins(a: int, b: int, c: int, n: int) returns (result: bool)
  requires a >= 0 && b >= 0 && c >= 0 && n >= 0
  ensures result == CanDistribute(a, b, c, n)
{
  var tot := a + b + c + n;
  if tot % 3 != 0 {
    forall A: int, B: int, C: int
      ensures !ValidDistribution(a, b, c, n, A, B, C)
    {
      if A >= 0 && B >= 0 && C >= 0 && A + B + C == n && a + A == b + B && a + A == c + C {
        assert 3 * (a + A) == tot;
      }
    }
    return false;
  }
  var des := tot / 3;
  if a > des || b > des || c > des {
    forall A: int, B: int, C: int
      ensures !ValidDistribution(a, b, c, n, A, B, C)
    {
      if A >= 0 && B >= 0 && C >= 0 && A + B + C == n && a + A == b + B && a + A == c + C {
        assert 3 * (a + A) == tot;
        assert tot == 3 * des;
        assert a + A == des;
      }
    }
    return false;
  }
  assert (des - a) + (des - b) + (des - c) == n by {
    assert 3 * des == tot;
  }
  assert ValidDistribution(a, b, c, n, des - a, des - b, des - c);
  return true;
}

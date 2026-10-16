ghost function Gcd(a: int, b: int): int
  requires a > 0 && b > 0
  decreases b
{
  if a % b == 0 then b
  else Gcd(b, a % b)
}

lemma MulLeMonotone(c: int, a: int, b: int)
  requires c > 0
  requires a <= b
  ensures c * a <= c * b
  decreases c
{
  if c > 1 {
    MulLeMonotone(c - 1, a, b);
  }
}

lemma ModSelfSmaller(a: int, b: int)
  requires 0 < a < b
  ensures a % b == a
{
  assert a == b * 0 + a;
  assert 0 <= a < b;
}

lemma ModSmaller(b: int, a: int)
  requires a > 0 && b > 0
  requires b % a != 0
  ensures 0 < b % a < a
{
}

lemma GcdSymmetry(a: int, b: int)
  requires 0 < a < b
  ensures Gcd(a, b) == Gcd(b, a)
{
  ModSelfSmaller(a, b);
  assert a % b == a;
  assert Gcd(a, b) == Gcd(b, a);
}

lemma GcdBound(a: int, b: int)
  requires 0 < a < b
  ensures Gcd(a, b) * 2 <= b
  decreases b, a
{
  ModSelfSmaller(a, b);
  assert a % b == a;
  assert Gcd(a, b) == Gcd(b, a);

  var r := b % a;
  if r == 0 {
    assert Gcd(b, a) == a;
    var k := b / a;
    assert b == a * k;
    assert k >= 2;
    MulLeMonotone(a, 2, k);
  } else {
    ModSmaller(b, a);
    assert 0 < r && r < a;
    assert Gcd(b, a) == Gcd(a, r);
    ModSelfSmaller(r, a);
    assert r % a == r;
    assert Gcd(r, a) == Gcd(a, r);
    GcdBound(r, a);
  }
}

method MaximumGCD(n: int) returns (result: int)
  requires n >= 2
  ensures exists a: int | 1 <= a && a < n :: exists b: int | a < b && b <= n :: Gcd(a, b) == result
  ensures forall a: int | 1 <= a && a < n :: forall b: int | a < b && b <= n :: Gcd(a, b) <= result
{
  result := n / 2;

  var wa := n / 2;
  var wb := 2 * wa;
  assert 1 <= wa && wa < n;
  assert wa < wb && wb <= n;
  assert wb % wa == 0;
  assert Gcd(wb, wa) == wa;
  assert Gcd(wa, wb) == wa;

  forall ai: int | 1 <= ai && ai < n
    ensures forall bi: int | ai < bi && bi <= n :: Gcd(ai, bi) <= result
  {
    forall bi: int | ai < bi && bi <= n
      ensures Gcd(ai, bi) <= result
    {
      GcdBound(ai, bi);
    }
  }
}

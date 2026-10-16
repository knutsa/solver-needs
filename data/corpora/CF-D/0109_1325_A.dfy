ghost function Min(a: int, b: int): int {
  if a <= b then a else b
}

ghost function Max(a: int, b: int): int {
  if a >= b then a else b
}

ghost predicate Divides(d: int, n: int)
  requires d > 0
{
  n % d == 0
}

ghost predicate IsGcd(g: int, a: int, b: int)
  requires a > 0 && b > 0 && g > 0
{
  Divides(g, a) && Divides(g, b) &&
  forall d :: 1 <= d <= Min(a, b) ==> (Divides(d, a) && Divides(d, b)) ==> d <= g
}

ghost predicate IsLcm(l: int, a: int, b: int)
  requires a > 0 && b > 0 && l > 0
{
  Divides(a, l) && Divides(b, l) &&
  forall m :: 1 <= m <= l ==> (Divides(a, m) && Divides(b, m)) ==> l <= m
}

ghost predicate ValidSolution(a: int, b: int, x: int)
{
  a > 0 && b > 0 && x > 0 &&
  exists g | 1 <= g <= Min(a, b) ::
    exists l | Max(a, b) <= l <= a * b ::
      IsGcd(g, a, b) && IsLcm(l, a, b) && g + l == x
}

lemma DivModLemma(b: int, m: int)
  requires b > 0
  requires 1 <= m <= b
  requires m % b == 0
  ensures m == b
{
  var q := m / b;
  assert m == q * b;
  if q <= 0 {
    assert m <= 0;
  }
  if q >= 2 {
    assert m >= 2 * b;
  }
  assert q == 1;
}

method EhAbAndGcd(x: int) returns (a: int, b: int)
  requires x >= 2
  ensures ValidSolution(a, b, x)
{
  a := 1;
  b := x - 1;

  ghost var g := 1;
  ghost var l := x - 1;

  // GCD(1, x-1) = 1
  assert Divides(g, a);
  assert Divides(g, b);
  assert IsGcd(g, a, b);

  // LCM(1, x-1) = x-1
  assert Divides(a, l);
  assert Divides(b, l);

  // For the LCM universally quantified part: if 1|m and (x-1)|m and 1<=m<=x-1, then m>=x-1
  forall m | 1 <= m <= l && Divides(a, m) && Divides(b, m)
    ensures l <= m
  {
    // b divides m means m % b == 0, and 1 <= m <= b, so m == b == l
    DivModLemma(b, m);
  }

  assert IsLcm(l, a, b);
  assert g + l == x;

  // Provide witnesses for the existentials
  assert 1 <= g <= Min(a, b);
  assert Max(a, b) <= l <= a * b;
  assert IsGcd(g, a, b) && IsLcm(l, a, b) && g + l == x;
}

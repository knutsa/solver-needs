ghost function GCD(a: int, b: int): int
  requires a > 0 && b >= 0
  ensures GCD(a, b) > 0
  decreases b
{
  if b == 0 then a else GCD(b, a % b)
}

ghost function LCM(a: int, b: int): int
  requires a > 0 && b > 0
{
  (a / GCD(a, b)) * b
}

ghost predicate ValidPair(x: int, y: int, l: int, r: int)
  requires l >= 1
{
  l <= x && x < y && y <= r && l <= LCM(x, y) && LCM(x, y) <= r
}

ghost predicate PairExists(l: int, r: int)
  requires l >= 1
{
  exists x | l <= x <= r :: exists y | x + 1 <= y <= r :: ValidPair(x, y, l, r)
}

lemma ProductNonNeg(a: int, b: int)
  requires a >= 0
  requires b >= 0
  ensures a * b >= 0
{}

lemma SumDivisible(a: int, b: int, g: int)
  requires g > 0
  requires a % g == 0
  requires b % g == 0
  ensures (a + b) % g == 0
{
  var k1 := a / g;
  var k2 := b / g;
  assert a == k1 * g;
  assert b == k2 * g;
  assert a + b == (k1 + k2) * g;
}

lemma DiffDivisible(a: int, b: int, g: int)
  requires g > 0
  requires a % g == 0
  requires b % g == 0
  ensures (a - b) % g == 0
{
  var k1 := a / g;
  var k2 := b / g;
  assert a == k1 * g;
  assert b == k2 * g;
  assert a - b == (k1 - k2) * g;
}

lemma MultipleOfMultiple(q: int, b: int, g: int)
  requires g > 0
  requires b % g == 0
  ensures (q * b) % g == 0
  decreases if q >= 0 then q else -q
{
  if q == 0 {
  } else if q > 0 {
    MultipleOfMultiple(q - 1, b, g);
    assert q * b == (q - 1) * b + b;
    SumDivisible((q - 1) * b, b, g);
  } else {
    MultipleOfMultiple(q + 1, b, g);
    assert q * b == (q + 1) * b - b;
    DiffDivisible((q + 1) * b, b, g);
  }
}

lemma GcdDividesBoth(a: int, b: int)
  requires a > 0 && b > 0
  ensures a % GCD(a, b) == 0
  ensures b % GCD(a, b) == 0
  decreases b
{
  if a % b == 0 {
  } else {
    var r := a % b;
    GcdDividesBoth(b, r);
    var g := GCD(a, b);
    assert b % g == 0;
    assert r % g == 0;
    var q := a / b;
    assert a == q * b + r;
    MultipleOfMultiple(q, b, g);
    SumDivisible(q * b, r, g);
  }
}

lemma GcdOfDoubleReverse(a: int)
  requires a > 0
  ensures GCD(2 * a, a) == a
{
  assert (2 * a) % a == 0;
}

lemma GcdOfDoubled(a: int)
  requires a > 0
  ensures GCD(a, 2 * a) == a
{
  assert a % (2 * a) == a;
  GcdOfDoubleReverse(a);
}

lemma LcmLowerBound(x: int, y: int)
  requires x > 0 && y > x
  ensures LCM(x, y) >= 2 * x
{
  GcdDividesBoth(x, y);
  var g := GCD(x, y);
  assert x % g == 0;
  assert y % g == 0;

  DiffDivisible(y, x, g);
  assert (y - x) % g == 0;
  assert y - x > 0;
  assert y - x >= g;

  var a := x / g;
  assert a * g == x;
  assert a >= 1;
  assert LCM(x, y) == a * y;

  // a * y >= a * (x + g): from y >= x + g and a >= 0
  assert y - (x + g) >= 0;
  ProductNonNeg(a, y - (x + g));
  assert a * (y - (x + g)) >= 0;
  assert a * y - a * (x + g) == a * (y - (x + g));
  assert a * y >= a * (x + g);

  // a * (x + g) == a * x + a * g == a * x + x
  assert a * (x + g) == a * x + a * g;
  assert a * y >= a * x + x;

  // a * x >= x: from a >= 1, x > 0
  ProductNonNeg(a - 1, x);
  assert (a - 1) * x >= 0;
  assert a * x - x == (a - 1) * x;
  assert a * x >= x;
  assert a * x + x >= 2 * x;
}

method LCMProblem(l: int, r: int) returns (x: int, y: int)
  requires l >= 1
  ensures (x == -1 && y == -1) || ValidPair(x, y, l, r)
  ensures (x == -1 && y == -1) <==> !PairExists(l, r)
{
  if l * 2 > r {
    forall xi: int, yi: int | l <= xi && xi < yi && yi <= r
      ensures !ValidPair(xi, yi, l, r)
    {
      LcmLowerBound(xi, yi);
    }
    return -1, -1;
  } else {
    GcdOfDoubled(l);
    assert GCD(l, 2 * l) == l;
    assert l / l == 1;
    assert LCM(l, 2 * l) == 2 * l;
    assert ValidPair(l, 2 * l, l, r);
    return l, l * 2;
  }
}

ghost predicate IsValidWindow(a: int, b: int, c1: int, r1: int, c2: int, r2: int)
{
  0 <= c1 <= c2 < a && 0 <= r1 <= r2 < b
}

ghost predicate WindowAvoidsDead(c1: int, r1: int, c2: int, r2: int, x: int, y: int)
{
  x < c1 || x > c2 || y < r1 || y > r2
}

ghost function WindowArea(c1: int, r1: int, c2: int, r2: int): int
{
  (c2 - c1 + 1) * (r2 - r1 + 1)
}

lemma MulMono(a1: int, a2: int, b1: int, b2: int)
  requires 0 <= a1 <= a2
  requires 0 <= b1 <= b2
  ensures a1 * b1 <= a2 * b2
{
  calc {
    a1 * b1;
    <= a2 * b1;
    <= a2 * b2;
  }
}

lemma WindowBoundLemma(a: int, b: int, c1: int, r1: int, c2: int, r2: int, x: int, y: int)
  requires a >= 1 && b >= 1
  requires 0 <= x < a && 0 <= y < b
  requires 0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b
  requires IsValidWindow(a, b, c1, r1, c2, r2)
  requires WindowAvoidsDead(c1, r1, c2, r2, x, y)
  ensures WindowArea(c1, r1, c2, r2) <= x * b
       || WindowArea(c1, r1, c2, r2) <= (a - x - 1) * b
       || WindowArea(c1, r1, c2, r2) <= y * a
       || WindowArea(c1, r1, c2, r2) <= (b - y - 1) * a
{
  var w := c2 - c1 + 1;
  var h := r2 - r1 + 1;

  if x < c1 {
    assert w <= a - x - 1;
    assert h <= b;
    MulMono(w, a - x - 1, h, b);
  } else if x > c2 {
    assert w <= x;
    assert h <= b;
    MulMono(w, x, h, b);
  } else if y < r1 {
    assert h <= b - y - 1;
    assert w <= a;
    MulMono(w, a, h, b - y - 1);
  } else {
    assert y > r2;
    assert h <= y;
    assert w <= a;
    MulMono(w, a, h, y);
  }
}

method DeadPixel(a: int, b: int, x: int, y: int) returns (area: int)
  requires a >= 1 && b >= 1
  requires 0 <= x < a && 0 <= y < b
  ensures area >= 0
  ensures forall c1, r1, c2, r2 ::
    (0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b &&
    IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y))
      ==> WindowArea(c1, r1, c2, r2) <= area
  ensures area == 0 ||
    (exists c1, r1, c2, r2 | 0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b ::
      IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y) &&
      WindowArea(c1, r1, c2, r2) == area)
{
  var v1 := x * b;
  var v2 := y * a;
  var v3 := (a - x - 1) * b;
  var v4 := (b - y - 1) * a;
  area := v1;
  if v2 > area { area := v2; }
  if v3 > area { area := v3; }
  if v4 > area { area := v4; }

  forall c1, r1, c2, r2 |
    0 <= c1 < a && 0 <= r1 < b && 0 <= c2 < a && 0 <= r2 < b &&
    IsValidWindow(a, b, c1, r1, c2, r2) && WindowAvoidsDead(c1, r1, c2, r2, x, y)
    ensures WindowArea(c1, r1, c2, r2) <= area
  {
    WindowBoundLemma(a, b, c1, r1, c2, r2, x, y);
  }

  if v1 >= v2 && v1 >= v3 && v1 >= v4 && v1 > 0 {
    assert x >= 1;
    assert IsValidWindow(a, b, 0, 0, x - 1, b - 1);
    assert WindowAvoidsDead(0, 0, x - 1, b - 1, x, y);
    assert WindowArea(0, 0, x - 1, b - 1) == x * b;
  } else if v2 >= v1 && v2 >= v3 && v2 >= v4 && v2 > 0 {
    assert y >= 1;
    assert IsValidWindow(a, b, 0, 0, a - 1, y - 1);
    assert WindowAvoidsDead(0, 0, a - 1, y - 1, x, y);
    assert WindowArea(0, 0, a - 1, y - 1) == y * a;
  } else if v3 >= v1 && v3 >= v2 && v3 >= v4 && v3 > 0 {
    assert x + 1 <= a - 1;
    assert IsValidWindow(a, b, x + 1, 0, a - 1, b - 1);
    assert WindowAvoidsDead(x + 1, 0, a - 1, b - 1, x, y);
    assert WindowArea(x + 1, 0, a - 1, b - 1) == (a - x - 1) * b;
  } else if v4 > 0 {
    assert y + 1 <= b - 1;
    assert IsValidWindow(a, b, 0, y + 1, a - 1, b - 1);
    assert WindowAvoidsDead(0, y + 1, a - 1, b - 1, x, y);
    assert WindowArea(0, y + 1, a - 1, b - 1) == (b - y - 1) * a;
  }
  return;
}

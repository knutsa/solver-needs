// Checks whether a specific allocation of grapes satisfies all constraints:
//   ga/gd/gm = green grapes to Andrew/Dmitry/Michal
//   pd/pm    = purple grapes to Dmitry/Michal
//   bm       = black grapes to Michal
// Andrew eats only green; Dmitry eats green or purple; Michal eats any type.
ghost predicate ValidAllocation(x: int, y: int, z: int, a: int, b: int, c: int,
                          ga: int, gd: int, pd: int, gm: int, pm: int, bm: int)
{
  ga >= 0 && gd >= 0 && pd >= 0 && gm >= 0 && pm >= 0 && bm >= 0 &&
  ga >= x &&
  gd + pd >= y &&
  gm + pm + bm >= z &&
  ga + gd + gm <= a &&
  pd + pm <= b &&
  bm <= c
}

// There exists a distribution of grapes making everyone happy.
// We fix Andrew's share at exactly x green (giving more wastes green grapes).
// We search over gd: how many green grapes Dmitry receives.
// Dmitry's purple share is y - gd; Michal receives all remaining grapes.
ghost predicate Feasible(x: int, y: int, z: int, a: int, b: int, c: int)
  requires x >= 0 && y >= 0 && z >= 0 && a >= 0 && b >= 0 && c >= 0
{
  var bound := if a - x < y then a - x else y;
  exists gd: int | 0 <= gd <= bound ::
    ValidAllocation(x, y, z, a, b, c,
                    x, gd, y - gd, a - x - gd, b - (y - gd), c)
}

lemma FeasibleTrue(x: int, y: int, z: int, a: int, b: int, c: int)
  requires x >= 0 && y >= 0 && z >= 0 && a >= 0 && b >= 0 && c >= 0
  requires a >= x && a + b >= x + y && a + b + c >= x + y + z
  ensures Feasible(x, y, z, a, b, c)
{
  var bound := if a - x < y then a - x else y;
  var w := if b >= y then 0 else y - b;

  assert 0 <= w;
  if b >= y {
    assert w == 0;
    assert w <= bound;
  } else {
    assert w == y - b;
    assert w <= y;
    assert w <= a - x;
    assert w <= bound;
  }

  assert x >= 0;
  assert w >= 0;
  assert y - w >= 0;
  assert a - x - w >= 0;
  assert b - (y - w) >= 0;
  assert c >= 0;
  assert x >= x;
  assert w + (y - w) >= y;
  assert (a - x - w) + (b - (y - w)) + c == a + b + c - x - y;
  assert a + b + c - x - y >= z;
  assert x + w + (a - x - w) == a;
  assert (y - w) + (b - (y - w)) == b;
  assert c <= c;

  assert ValidAllocation(x, y, z, a, b, c, x, w, y - w, a - x - w, b - (y - w), c);
}

lemma FeasibleFalse(x: int, y: int, z: int, a: int, b: int, c: int)
  requires x >= 0 && y >= 0 && z >= 0 && a >= 0 && b >= 0 && c >= 0
  requires !(a >= x && a + b >= x + y && a + b + c >= x + y + z)
  ensures !Feasible(x, y, z, a, b, c)
{
  var bound := if a - x < y then a - x else y;
  forall gd | 0 <= gd <= bound
    ensures !ValidAllocation(x, y, z, a, b, c, x, gd, y - gd, a - x - gd, b - (y - gd), c)
  {
    if !(a >= x) {
    } else if !(a + b >= x + y) {
      if gd < y - b {
        assert b - (y - gd) < 0;
      } else {
        assert a - x - gd <= a + b - x - y;
        assert a + b - x - y < 0;
      }
    } else {
      assert (a - x - gd) + (b - (y - gd)) + c == a + b + c - x - y;
    }
  }
}

method GotAnyGrapes(x: int, y: int, z: int, a: int, b: int, c: int) returns (result: bool)
  requires x >= 0 && y >= 0 && z >= 0 && a >= 0 && b >= 0 && c >= 0
  ensures result == Feasible(x, y, z, a, b, c)
{
  var a' := a;
  var b' := b;
  var c' := c;

  c' := c' - z;
  if c' < 0 {
    b' := b' + c';
  }
  b' := b' - y;
  if b' < 0 {
    a' := a' + b';
  }
  a' := a' - x;

  result := a' >= 0;

  if result {
    FeasibleTrue(x, y, z, a, b, c);
  } else {
    FeasibleFalse(x, y, z, a, b, c);
  }
}

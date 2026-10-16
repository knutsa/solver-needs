ghost predicate MeetAt(x: int, y: int, a: int, b: int, t: int)
{
  t >= 1 && x + t * a == y - t * b
}

method TwoRabbits(x: int, y: int, a: int, b: int) returns (t: int)
  requires x < y
  requires a >= 1
  requires b >= 1
  ensures t == -1 || t >= 1
  ensures t >= 1 ==> MeetAt(x, y, a, b, t)
  ensures t == -1 ==> forall t' :: t' >= 1 ==> !MeetAt(x, y, a, b, t')
{
  var z := y - x;
  var c := a + b;
  if z % c != 0 {
    t := -1;
    var q := z / c;
    var r := z % c;
    assert z == q * c + r;
    assert r > 0;
    assert r < c;
    forall t' | t' >= 1
      ensures !MeetAt(x, y, a, b, t')
    {
      if MeetAt(x, y, a, b, t') {
        assert x + t' * a == y - t' * b;
        assert t' * a + t' * b == y - x;
        assert t' * (a + b) == z;
        assert t' * c == z;
        // z = q*c + r, so t'*c = q*c + r, so (t'-q)*c = r
        assert t' * c - q * c == r;
        assert (t' - q) * c == r;
        if t' == q {
          assert r == 0;
        } else if t' > q {
          assert (t' - q) >= 1;
          assert (t' - q) * c >= 1 * c;
          assert r >= c;
        } else {
          assert t' - q <= -1;
          assert (t' - q) * c <= -1 * c;
          assert r <= -c;
        }
      }
    }
  } else {
    t := z / c;
    assert t * c == z;
    assert t * (a + b) == y - x;
    assert t * a + t * b == y - x;
    assert x + t * a == y - t * b;
  }
}

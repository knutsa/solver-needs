ghost predicate IsTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

ghost predicate CanFormTriangleWithKMinutes(a: int, b: int, c: int, k: int)
{
  k >= 0 &&
  exists da | 0 <= da <= k ::
    exists db | 0 <= db <= k - da ::
      IsTriangle(a + da, b + db, c + (k - da - db))
}

ghost predicate IsMinimalMinutes(a: int, b: int, c: int, minutes: int)
{
  CanFormTriangleWithKMinutes(a, b, c, minutes) &&
  forall k :: 0 <= k < minutes ==> !CanFormTriangleWithKMinutes(a, b, c, k)
}

lemma ExistsWitness(a: int, b: int, c: int, k: int, wda: int, wdb: int)
  requires k >= 0
  requires 0 <= wda <= k
  requires 0 <= wdb <= k - wda
  requires IsTriangle(a + wda, b + wdb, c + (k - wda - wdb))
  ensures CanFormTriangleWithKMinutes(a, b, c, k)
{
  assert exists db | 0 <= db <= k - wda ::
    IsTriangle(a + wda, b + db, c + (k - wda - db)) by {
    assert 0 <= wdb <= k - wda;
    assert IsTriangle(a + wda, b + wdb, c + (k - wda - wdb));
  }
  assert exists da | 0 <= da <= k ::
    exists db | 0 <= db <= k - da ::
      IsTriangle(a + da, b + db, c + (k - da - db)) by {
    assert 0 <= wda <= k;
  }
}

lemma NotTriangleWhenSumTooSmall(a: int, b: int, c: int, m: int, k: int)
  requires a >= 1 && b >= 1 && c >= 1
  requires m >= a && m >= b && m >= c
  requires m == a || m == b || m == c
  requires 0 <= k
  requires a + b + c + k <= 2 * m
  ensures !CanFormTriangleWithKMinutes(a, b, c, k)
{
  forall da | 0 <= da <= k
    ensures !(exists db | 0 <= db <= k - da ::
      IsTriangle(a + da, b + db, c + (k - da - db)))
  {
    forall db | 0 <= db <= k - da
      ensures !IsTriangle(a + da, b + db, c + (k - da - db))
    {
      var x := a + da;
      var y := b + db;
      var z := c + (k - da - db);
      assert x + y + z == a + b + c + k;
      if m == a {
        assert x >= m;
        assert y + z <= x;
      } else if m == b {
        assert y >= m;
        assert x + z <= y;
      } else {
        assert z >= m;
        assert x + y <= z;
      }
    }
  }
}

method MakeTriangle(a: int, b: int, c: int) returns (minutes: int)
  requires a >= 1 && b >= 1 && c >= 1
  ensures minutes >= 0
  ensures IsMinimalMinutes(a, b, c, minutes)
{
  var m := a;
  if b > m { m := b; }
  if c > m { m := c; }
  var diff := m - a - b - c + m + 1;
  if diff < 0 {
    minutes := 0;
    assert a + b + c > 2 * m;
    assert IsTriangle(a, b, c);
    ExistsWitness(a, b, c, 0, 0, 0);
  } else {
    minutes := diff;
    assert minutes == 2 * m - a - b - c + 1;
    assert minutes >= 0;

    if m == a {
      // Add all to b: da=0, db=minutes, so sides (a, b+minutes, c)
      // b+minutes+c = a+1 > a; a+c > b+minutes since 2c>1; a+b+minutes > c since 2a+1>2c
      assert IsTriangle(a + 0, b + minutes, c + (minutes - 0 - minutes));
      ExistsWitness(a, b, c, minutes, 0, minutes);
    } else if m == b {
      // Add all to a: da=minutes, db=0, so sides (a+minutes, b, c)
      assert IsTriangle(a + minutes, b + 0, c + (minutes - minutes - 0));
      ExistsWitness(a, b, c, minutes, minutes, 0);
    } else {
      assert m == c;
      // Add all to a: da=minutes, db=0, so sides (a+minutes, b, c)
      assert IsTriangle(a + minutes, b + 0, c + (minutes - minutes - 0));
      ExistsWitness(a, b, c, minutes, minutes, 0);
    }

    forall k | 0 <= k < minutes
      ensures !CanFormTriangleWithKMinutes(a, b, c, k)
    {
      assert a + b + c + k <= 2 * m;
      NotTriangleWhenSumTooSmall(a, b, c, m, k);
    }
  }
}

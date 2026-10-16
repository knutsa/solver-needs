// A valid assignment: enough pens for all lectures, enough pencils for all
// practical classes, and they fit in the pencilcase.
ghost predicate ValidAssignment(x: int, y: int, a: int, b: int, c: int, d: int, k: int)
{
  x >= 0 && y >= 0 && x * c >= a && y * d >= b && x + y <= k
}

// The problem is feasible iff some valid assignment of pens and pencils exists.
ghost predicate Feasible(a: int, b: int, c: int, d: int, k: int)
{
  exists x :: exists y :: ValidAssignment(x, y, a, b, c, d, k)
}

lemma MulLe(a: int, b: int, c: int)
  requires a <= b && c >= 0
  ensures a * c <= b * c
{}

lemma CeilDivLower(a: int, c: int)
  requires a >= 1 && c >= 1
  ensures ((a + c - 1) / c) * c >= a
  ensures (a + c - 1) / c >= 0
{
  var q := (a + c - 1) / c;
  var r := (a + c - 1) % c;
  assert q * c + r == a + c - 1;
  assert r >= 0;
  // q * c = a + c - 1 - r >= a + c - 1 - (c - 1) = a
}

lemma CeilDivMinimal(a: int, c: int, x: int)
  requires a >= 1 && c >= 1 && x >= 0 && x * c >= a
  ensures x >= (a + c - 1) / c
{
  var q := (a + c - 1) / c;
  if x < q {
    var r := (a + c - 1) % c;
    assert q * c + r == a + c - 1;
    assert q * c == a + c - 1 - r;
    assert (q - 1) * c == q * c - c;
    assert (q - 1) * c == a - 1 - r;
    assert (q - 1) * c <= a - 1;
    MulLe(x, q - 1, c);
    assert x * c <= (q - 1) * c;
    assert x * c <= a - 1;
    assert false;
  }
}

method PensAndPencils(a: int, b: int, c: int, d: int, k: int) returns (x: int, y: int)
  requires a >= 1 && b >= 1 && c >= 1 && d >= 1 && k >= 1
  ensures Feasible(a, b, c, d, k) ==> ValidAssignment(x, y, a, b, c, d, k)
  ensures !Feasible(a, b, c, d, k) ==> x == -1
{
  var pens := (a + c - 1) / c;
  var pencils := (b + d - 1) / d;

  CeilDivLower(a, c);
  CeilDivLower(b, d);

  if pens + pencils <= k {
    assert ValidAssignment(pens, pencils, a, b, c, d, k);
    return pens, pencils;
  } else {
    assert forall x0, y0 :: !ValidAssignment(x0, y0, a, b, c, d, k) by {
      forall x0, y0
        ensures !ValidAssignment(x0, y0, a, b, c, d, k)
      {
        if x0 >= 0 && y0 >= 0 && x0 * c >= a && y0 * d >= b {
          CeilDivMinimal(a, c, x0);
          CeilDivMinimal(b, d, y0);
          assert x0 >= pens;
          assert y0 >= pencils;
          assert x0 + y0 >= pens + pencils > k;
        }
      }
    }
    assert !Feasible(a, b, c, d, k);
    return -1, 0;
  }
}

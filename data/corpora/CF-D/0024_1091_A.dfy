ghost predicate Beautiful(ny: int, nb: int, nr: int)
{
  nb == ny + 1 && nr == nb + 1
}

ghost predicate ValidChoice(y: int, b: int, r: int, ny: int, nb: int, nr: int)
{
  0 <= ny <= y && 0 <= nb <= b && 0 <= nr <= r && Beautiful(ny, nb, nr)
}

method MaxOrnaments(y: int, b: int, r: int) returns (total: int)
  requires y >= 1 && b >= 2 && r >= 3
  ensures exists ny | 0 <= ny <= y ::
            ValidChoice(y, b, r, ny, ny + 1, ny + 2) &&
            total == ny + (ny + 1) + (ny + 2)
  ensures forall ny | 0 <= ny <= y ::
            ValidChoice(y, b, r, ny, ny + 1, ny + 2) ==>
              ny + (ny + 1) + (ny + 2) <= total
{
  var m := y;
  if b - 1 < m { m := b - 1; }
  if r - 2 < m { m := r - 2; }
  total := 3 * m + 3;

  // Prove the existential: m is a valid choice
  assert ValidChoice(y, b, r, m, m + 1, m + 2);

  // Prove optimality: for any valid ny, ny <= m so 3*ny+3 <= 3*m+3
  forall ny | 0 <= ny <= y
    ensures ValidChoice(y, b, r, ny, ny + 1, ny + 2) ==>
              ny + (ny + 1) + (ny + 2) <= total
  {
    if ValidChoice(y, b, r, ny, ny + 1, ny + 2) {
      assert ny <= y;
      assert ny + 1 <= b;
      assert ny + 2 <= r;
      assert ny <= m;
    }
  }
}

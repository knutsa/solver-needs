ghost predicate ValidPair(x: int, y: int, l: int, r: int)
{
  l <= x <= r && l <= y <= r && x != y && x > 0 && y % x == 0
}

method FindDivisible(l: int, r: int) returns (x: int, y: int)
  requires l >= 1
  requires 2 * l <= r
  ensures ValidPair(x, y, l, r)
{
  x := l;
  y := 2 * l;
}

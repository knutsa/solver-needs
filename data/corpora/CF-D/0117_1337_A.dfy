ghost predicate IsTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

ghost predicate InRange(x: int, y: int, z: int, a: int, b: int, c: int, d: int)
{
  a <= x <= b && b <= y <= c && c <= z <= d
}

ghost predicate IsValidSolution(x: int, y: int, z: int, a: int, b: int, c: int, d: int)
{
  InRange(x, y, z, a, b, c, d) && IsTriangle(x, y, z)
}

method IchihimeAndTriangle(a: int, b: int, c: int, d: int) returns (x: int, y: int, z: int)
  requires 1 <= a <= b <= c <= d
  ensures IsValidSolution(x, y, z, a, b, c, d)
{
  x := b;
  y := c;
  z := c;
}

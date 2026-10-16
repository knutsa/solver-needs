// The generalized polygon inequality: each side of a quadrilateral
// must be strictly less than the sum of the other three sides.
// This is the necessary and sufficient condition for four positive
// lengths to form a non-degenerate simple quadrilateral.
ghost predicate QuadrilateralInequality(a: int, b: int, c: int, d: int)
{
  a < b + c + d &&
  b < a + c + d &&
  c < a + b + d &&
  d < a + b + c
}

ghost predicate CanFormQuadrilateral(a: int, b: int, c: int, d: int)
{
  a > 0 && b > 0 && c > 0 && d > 0 &&
  QuadrilateralInequality(a, b, c, d)
}

method Fence(a: int, b: int, c: int) returns (d: int)
  requires a > 0 && b > 0 && c > 0
  ensures d > 0
  ensures CanFormQuadrilateral(a, b, c, d)
{
  d := a + b + c - 1;
}

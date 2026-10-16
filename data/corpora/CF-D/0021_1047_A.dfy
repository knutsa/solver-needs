ghost predicate IsValidSplit(n: int, a: int, b: int, c: int)
{
  a > 0 && b > 0 && c > 0 &&
  a + b + c == n &&
  a % 3 != 0 && b % 3 != 0 && c % 3 != 0
}

method LittleCLoves3(n: int) returns (a: int, b: int, c: int)
  requires n >= 3
  ensures IsValidSplit(n, a, b, c)
{
  a := 1;
  b := 1;
  c := n - 2;
  if c % 3 == 0 {
    c := c - 1;
    b := b + 1;
  }
}

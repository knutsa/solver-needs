ghost function DigitSum(n: int): int
  requires n >= 0
  decreases n
{
  if n == 0 then 0
  else n % 10 + DigitSum(n / 10)
}

ghost predicate IsInteresting(n: int)
  requires n >= 0
{
  DigitSum(n) == 18
}

method SumDigits(x: int) returns (s: int)
  requires x >= 0
  ensures s == DigitSum(x)
  decreases *
{
  s := 0;
  var tmp := x;
  while tmp > 0
    invariant tmp >= 0
    invariant s + DigitSum(tmp) == DigitSum(x)
    decreases *
  {
    s := s + tmp % 10;
    tmp := tmp / 10;
  }
}

method NearestInterestingNumber(a: int) returns (n: int)
  requires a >= 1
  ensures n >= a
  ensures IsInteresting(n)
  ensures forall k :: a <= k < n ==> !IsInteresting(k)
  decreases *
{
  n := a;
  var s := SumDigits(n);
  while s != 18
    invariant n >= a
    invariant s == DigitSum(n)
    invariant forall k :: a <= k < n ==> !IsInteresting(k)
    decreases *
  {
    n := n + 1;
    s := SumDigits(n);
  }
}

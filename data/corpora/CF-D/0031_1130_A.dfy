ghost predicate IsPositiveAfterDiv(x: int, d: int)
  requires d != 0
{
  (x > 0 && d > 0) || (x < 0 && d < 0)
}

ghost function CountPositiveAfterDiv(a: seq<int>, d: int): int
  requires d != 0
  decreases |a|
{
  if |a| == 0 then 0
  else CountPositiveAfterDiv(a[..|a|-1], d)
       + (if IsPositiveAfterDiv(a[|a|-1], d) then 1 else 0)
}

ghost function CeilHalf(n: int): int
{
  (n + 1) / 2
}

ghost function CountPositive(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0
  else CountPositive(a[..|a|-1]) + (if a[|a|-1] > 0 then 1 else 0)
}

ghost function CountNegative(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0
  else CountNegative(a[..|a|-1]) + (if a[|a|-1] < 0 then 1 else 0)
}

lemma CountPosDivPos(a: seq<int>, d: int)
  requires d > 0
  ensures CountPositiveAfterDiv(a, d) == CountPositive(a)
  decreases |a|
{
  if |a| > 0 {
    CountPosDivPos(a[..|a|-1], d);
  }
}

lemma CountPosDivNeg(a: seq<int>, d: int)
  requires d < 0
  ensures CountPositiveAfterDiv(a, d) == CountNegative(a)
  decreases |a|
{
  if |a| > 0 {
    CountPosDivNeg(a[..|a|-1], d);
  }
}

method BePositive(a: seq<int>) returns (d: int)
  ensures d != 0 ==> -1000 <= d <= 1000
                      && CountPositiveAfterDiv(a, d) >= CeilHalf(|a|)
  ensures d == 0 ==> (forall d' :: d' == 0 || CountPositiveAfterDiv(a, d') < CeilHalf(|a|))
{
  var n := |a|;
  var pcount := 0;
  var ncount := 0;
  var zcount := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant pcount == CountPositive(a[..i])
    invariant ncount == CountNegative(a[..i])
  {
    assert a[..i+1] == a[..i] + [a[i]];
    if a[i] > 0 {
      pcount := pcount + 1;
    } else if a[i] < 0 {
      ncount := ncount + 1;
    } else {
      zcount := zcount + 1;
    }
    i := i + 1;
  }
  assert a[..n] == a;
  var half := (n + 1) / 2;
  if pcount >= half {
    d := 1;
    CountPosDivPos(a, 1);
  } else if ncount >= half {
    d := -1;
    CountPosDivNeg(a, -1);
  } else {
    d := 0;
    forall d' | d' != 0
      ensures CountPositiveAfterDiv(a, d') < CeilHalf(|a|)
    {
      if d' > 0 {
        CountPosDivPos(a, d');
      } else {
        CountPosDivNeg(a, d');
      }
    }
  }
}

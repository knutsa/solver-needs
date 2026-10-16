ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}


ghost predicate NoLoss(price: int, a: seq<int>)
  requires |a| > 0
{
  price * |a| >= Sum(a)
}

ghost predicate IsMinimalEqualPrice(price: int, a: seq<int>)
  requires |a| > 0
{
  NoLoss(price, a) && !NoLoss(price - 1, a)
}

method EqualizePrice(a: seq<int>) returns (price: int)
  requires |a| > 0
  ensures IsMinimalEqualPrice(price, a)
{
  var s := 0;
  var n := |a|;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant s == Sum(a[..i])
  {
    assert a[..i+1] == a[..i] + [a[i]];
    // Inlined from SumAppend(a[..i], a[i])
    if |(a[..i])| == 0 {
    assert (a[..i]) + [(a[i])] == [(a[i])];
    } else {
    assert ((a[..i]) + [(a[i])])[..|(a[..i]) + [(a[i])]| - 1] == (a[..i]);
    assert ((a[..i]) + [(a[i])])[|(a[..i]) + [(a[i])]| - 1] == (a[i]);
    }
    assert Sum(a[..i] + [a[i]]) == Sum(a[..i]) + a[i];
    s := s + a[i];
    i := i + 1;
  }
  assert a[..n] == a;
  // Now s == Sum(a)

  price := (s + n - 1) / n;

  // Prove IsMinimalEqualPrice(price, a)
  var r := s % n;
  assert s == (s / n) * n + r;

  if r == 0 {
    assert s + n - 1 == (s / n) * n + (n - 1);
    assert 0 <= n - 1 < n;
    assert (s + n - 1) / n == s / n;
    assert price == s / n;
    assert price * n == s;
    assert price * n >= Sum(a);
    assert (price - 1) * n == s - n;
    assert (price - 1) * n < Sum(a);
  } else {
    assert r > 0;
    assert s + n - 1 == (s / n + 1) * n + (r - 1);
    assert 0 <= r - 1 < n;
    assert (s + n - 1) / n == s / n + 1;
    assert price == s / n + 1;
    assert price * n == s - r + n;
    assert price * n > s;
    assert price * n >= Sum(a);
    assert (price - 1) * n == s - r;
    assert (price - 1) * n < Sum(a);
  }
}

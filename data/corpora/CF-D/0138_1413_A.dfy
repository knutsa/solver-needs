ghost function DotProduct(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
  decreases |a|
{
  if |a| == 0 then 0
  else DotProduct(a[..|a|-1], b[..|b|-1]) + a[|a|-1] * b[|b|-1]
}

ghost predicate AllNonZero(s: seq<int>) {
  forall i | 0 <= i < |s| :: s[i] != 0
}

ghost predicate AllBounded(s: seq<int>, bound: int) {
  forall i | 0 <= i < |s| :: -bound <= s[i] <= bound
}

ghost predicate ValidSolution(a: seq<int>, b: seq<int>) {
  |a| == |b|
  && AllNonZero(b)
  && AllBounded(b, 100)
  && DotProduct(a, b) == 0
}

lemma DotProductAppend(a: seq<int>, b: seq<int>, x: int, y: int)
  requires |a| == |b|
  ensures DotProduct(a + [x], b + [y]) == DotProduct(a, b) + x * y
{
  var a' := a + [x];
  var b' := b + [y];
  assert a'[..|a'|-1] == a;
  assert b'[..|b'|-1] == b;
}

method FindSasuke(a: seq<int>) returns (b: seq<int>)
  requires |a| % 2 == 0
  requires AllNonZero(a)
  requires AllBounded(a, 100)
  ensures ValidSolution(a, b)
{
  b := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |b| == i
    invariant AllNonZero(b)
    invariant AllBounded(b, 100)
    invariant i % 2 == 0 ==> DotProduct(a[..i], b) == 0
    invariant i % 2 == 1 ==> DotProduct(a[..i], b) == a[i - 1] * a[i]
  {
    if i % 2 == 0 {
      DotProductAppend(a[..i], b, a[i], a[i + 1]);
      assert a[..i] + [a[i]] == a[..i + 1];
      b := b + [a[i + 1]];
    } else {
      DotProductAppend(a[..i], b, a[i], -a[i - 1]);
      assert a[..i] + [a[i]] == a[..i + 1];
      b := b + [-a[i - 1]];
    }
    i := i + 1;
  }
  assert a[..|a|] == a;
}

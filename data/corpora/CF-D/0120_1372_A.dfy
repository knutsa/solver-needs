ghost predicate InRange(a: seq<int>)
{
  forall i | 0 <= i < |a| :: 1 <= a[i] <= 1000
}

ghost predicate NoTripleSum(a: seq<int>)
{
  forall x, y, z | 0 <= x < |a| && 0 <= y < |a| && 0 <= z < |a| ::
    a[x] + a[y] != a[z]
}

ghost predicate IsComplete(a: seq<int>)
{
  InRange(a) && NoTripleSum(a)
}

method Solve(n: int) returns (a: seq<int>)
  requires n >= 0
  ensures |a| == n
  ensures IsComplete(a)
{
  a := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |a| == i
    invariant forall j | 0 <= j < |a| :: a[j] == 1
  {
    a := a + [1];
    i := i + 1;
  }
}

method TestSolve(ns: seq<int>)
  requires forall i | 0 <= i < |ns| :: ns[i] >= 0
{
  for i := 0 to |ns| {
    var r := Solve(ns[i]);
    expect |r| == ns[i];
    for j := 0 to |r| {
      expect r[j] == 1;
    }
  }
}

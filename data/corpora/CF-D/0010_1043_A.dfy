ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

// k is valid: each student can give a[i] votes to Elodreip (needs k >= a[i])
ghost predicate ValidK(a: seq<int>, k: int)
{
  forall i :: 0 <= i < |a| ==> k >= a[i]
}

// Awruk wins: his total (k*n - sum(a)) strictly exceeds Elodreip's total (sum(a))
ghost predicate AwrukWins(a: seq<int>, k: int)
{
  k * |a| - Sum(a) > Sum(a)
}

// k is the smallest value that is both valid and winning
ghost predicate IsSmallestWinningK(a: seq<int>, k: int)
  requires |a| > 0
{
  ValidK(a, k) && AwrukWins(a, k) &&
  forall k' :: 0 <= k' < k ==> !(ValidK(a, k') && AwrukWins(a, k'))
}

lemma SumAppend(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures Sum(a[..i+1]) == Sum(a[..i]) + a[i]
{
  assert a[..i+1][..i] == a[..i];
}

method Elections(a: seq<int>) returns (k: int)
  requires |a| > 0
  requires forall i :: 0 <= i < |a| ==> a[i] >= 0
  ensures IsSmallestWinningK(a, k)
{
  var s := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant s == Sum(a[..i])
  {
    SumAppend(a, i);
    s := s + a[i];
    i := i + 1;
  }
  assert a[..|a|] == a;

  var m := a[0];
  i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant forall j :: 0 <= j < i ==> m >= a[j]
    invariant exists j :: 0 <= j < i && m == a[j]
  {
    if a[i] > m {
      m := a[i];
    }
    i := i + 1;
  }

  k := m;
  while k * |a| - s <= s
    invariant k >= m
    invariant forall k' :: m <= k' < k ==> k' * |a| - s <= s
    decreases 2 * s + |a| - k * |a|
  {
    k := k + 1;
  }

  assert ValidK(a, k);
  assert AwrukWins(a, k);

  forall k' | 0 <= k' < k
    ensures !(ValidK(a, k') && AwrukWins(a, k'))
  {
    if k' < m {
      var j :| 0 <= j < |a| && m == a[j];
      assert !ValidK(a, k');
    } else {
      assert k' * |a| - s <= s;
      assert !AwrukWins(a, k');
    }
  }
}

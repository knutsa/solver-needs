ghost predicate InRange(s: seq<int>)
{
  forall i | 0 <= i < |s| :: 1 <= s[i] <= |s|
}

ghost predicate AllDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < |s| && 0 <= j < |s| && i != j :: s[i] != s[j]
}

ghost predicate IsPermutation(p: seq<int>)
{
  InRange(p) && AllDistinct(p)
}

ghost function AdjacentSums(p: seq<int>): seq<int>
  decreases |p|
{
  if |p| < 2 then []
  else if |p| == 2 then [p[0] + p[1]]
  else [p[0] + p[1]] + AdjacentSums(p[1..])
}

ghost predicate SameFingerprint(p: seq<int>, q: seq<int>)
{
  multiset(AdjacentSums(p)) == multiset(AdjacentSums(q))
}

lemma AdjacentSumsLength(s: seq<int>)
  requires |s| >= 2
  ensures |AdjacentSums(s)| == |s| - 1
  decreases |s|
{
  if |s| == 2 {
  } else {
    AdjacentSumsLength(s[1..]);
  }
}

lemma AdjacentSumsElement(s: seq<int>, k: int)
  requires |s| >= 2
  requires 0 <= k < |s| - 1
  ensures |AdjacentSums(s)| == |s| - 1
  ensures AdjacentSums(s)[k] == s[k] + s[k+1]
  decreases |s|
{
  AdjacentSumsLength(s);
  if |s| == 2 {
    assert k == 0;
  } else {
    if k == 0 {
    } else {
      AdjacentSumsElement(s[1..], k - 1);
    }
  }
}

lemma SeqReverseMultiset(s: seq<int>, r: seq<int>)
  requires |s| == |r|
  requires forall k | 0 <= k < |s| :: r[k] == s[|s| - 1 - k]
  ensures multiset(s) == multiset(r)
  decreases |s|
{
  if |s| == 0 {
  } else {
    var n := |s|;
    assert r == r[..n-1] + [r[n-1]];
    assert s == [s[0]] + s[1..];

    forall k {:trigger r[..n-1][k]} | 0 <= k < n - 1
      ensures r[..n-1][k] == s[1..][n - 2 - k]
    {
      assert r[..n-1][k] == r[k];
      assert r[k] == s[n - 1 - k];
      assert s[1..][n - 2 - k] == s[n - 1 - k];
    }

    SeqReverseMultiset(s[1..], r[..n-1]);
  }
}

method PermutationForgery(p: seq<int>) returns (p': seq<int>)
  requires |p| >= 2
  requires IsPermutation(p)
  ensures |p'| == |p|
  ensures IsPermutation(p')
  ensures p' != p
  ensures SameFingerprint(p, p')
{
  p' := [];
  var i := |p|;
  while i > 0
    invariant 0 <= i <= |p|
    invariant |p'| == |p| - i
    invariant forall j | 0 <= j < |p'| :: p'[j] == p[|p| - 1 - j]
  {
    i := i - 1;
    p' := p' + [p[i]];
  }

  var n := |p|;

  // Prove p' != p: p'[0] == p[n-1] != p[0] since AllDistinct and n >= 2
  assert p'[0] == p[n - 1];
  assert p[0] != p[n - 1];

  // Prove SameFingerprint
  AdjacentSumsLength(p);
  AdjacentSumsLength(p');

  forall k {:trigger AdjacentSums(p')[k]} | 0 <= k < n - 1
    ensures AdjacentSums(p')[k] == AdjacentSums(p)[n - 2 - k]
  {
    AdjacentSumsElement(p', k);
    AdjacentSumsElement(p, n - 2 - k);
    assert p'[k] == p[n - 1 - k];
    assert p'[k + 1] == p[n - 2 - k];
  }

  SeqReverseMultiset(AdjacentSums(p), AdjacentSums(p'));
}

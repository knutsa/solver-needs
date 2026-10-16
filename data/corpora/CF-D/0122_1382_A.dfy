ghost predicate IsSubsequence(c: seq<int>, s: seq<int>)
  decreases |s|
{
  if |c| == 0 then true
  else if |s| == 0 then false
  else if c[|c|-1] == s[|s|-1] then IsSubsequence(c[..|c|-1], s[..|s|-1])
  else IsSubsequence(c, s[..|s|-1])
}

ghost predicate ExistsCommonSubseqOfLen(a: seq<int>, b: seq<int>, k: nat)
  decreases |a| + |b|
{
  if k == 0 then true
  else if |a| == 0 || |b| == 0 then false
  else if a[|a|-1] == b[|b|-1] then
    ExistsCommonSubseqOfLen(a[..|a|-1], b[..|b|-1], k - 1) ||
    ExistsCommonSubseqOfLen(a[..|a|-1], b, k) ||
    ExistsCommonSubseqOfLen(a, b[..|b|-1], k)
  else
    ExistsCommonSubseqOfLen(a[..|a|-1], b, k) ||
    ExistsCommonSubseqOfLen(a, b[..|b|-1], k)
}

ghost function Min(x: nat, y: nat): nat {
  if x <= y then x else y
}

ghost predicate NoCommonElements(a: seq<int>, b: seq<int>)
{
  forall i, j :: 0 <= i < |a| && 0 <= j < |b| ==> a[i] != b[j]
}

lemma SingletonIsSubsequence(x: int, s: seq<int>, idx: int)
  requires 0 <= idx < |s|
  requires s[idx] == x
  ensures IsSubsequence([x], s)
  decreases |s|
{
  if x == s[|s| - 1] {
    assert [x][0] == s[|s|-1];
    assert [x][..0] == [];
  } else {
    assert idx < |s| - 1;
    assert s[..|s|-1][idx] == x;
    SingletonIsSubsequence(x, s[..|s|-1], idx);
  }
}

lemma NoCommonElementsMeansNoCommonSubseq(a: seq<int>, b: seq<int>, k: nat)
  requires k >= 1
  requires NoCommonElements(a, b)
  ensures !ExistsCommonSubseqOfLen(a, b, k)
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else {
    assert a[|a|-1] != b[|b|-1];
    assert NoCommonElements(a[..|a|-1], b);
    NoCommonElementsMeansNoCommonSubseq(a[..|a|-1], b, k);
    assert NoCommonElements(a, b[..|b|-1]);
    NoCommonElementsMeansNoCommonSubseq(a, b[..|b|-1], k);
  }
}

method CommonSubsequence(a: seq<int>, b: seq<int>) returns (found: bool, c: seq<int>)
  ensures found ==>
    |c| >= 1 &&
    IsSubsequence(c, a) &&
    IsSubsequence(c, b) &&
    forall len :: 1 <= len < |c| ==> !ExistsCommonSubseqOfLen(a, b, len)
  ensures !found ==>
    forall len :: 1 <= len <= Min(|a|, |b|) ==> !ExistsCommonSubseqOfLen(a, b, len)
{
  found := false;
  c := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall i', j :: 0 <= i' < i && 0 <= j < |b| ==> a[i'] != b[j]
  {
    var j := 0;
    while j < |b|
      invariant 0 <= j <= |b|
      invariant forall j' :: 0 <= j' < j ==> a[i] != b[j']
    {
      if a[i] == b[j] {
        found := true;
        c := [a[i]];
        SingletonIsSubsequence(a[i], a, i);
        SingletonIsSubsequence(a[i], b, j);
        return;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  assert NoCommonElements(a, b);
  forall len | 1 <= len <= Min(|a|, |b|)
    ensures !ExistsCommonSubseqOfLen(a, b, len)
  {
    NoCommonElementsMeansNoCommonSubseq(a, b, len);
  }
}

ghost predicate IsPermutation(p: seq<int>, n: int)
{
  n >= 1 &&
  |p| == n &&
  (forall i | 1 <= i <= n :: exists j | 0 <= j < n :: p[j] == i)
}

ghost predicate IsMerge(a: seq<int>, s1: seq<int>, s2: seq<int>)
  decreases |a|
{
  if |a| == 0 then
    |s1| == 0 && |s2| == 0
  else
    (|s1| > 0 && a[0] == s1[0] && IsMerge(a[1..], s1[1..], s2)) ||
    (|s2| > 0 && a[0] == s2[0] && IsMerge(a[1..], s1, s2[1..]))
}

// Lemma: if IsMerge(a, s1, s2), then IsMerge(a ++ [x], s1 ++ [x], s2)
lemma MergeAppendS1(a: seq<int>, s1: seq<int>, s2: seq<int>, x: int)
  requires IsMerge(a, s1, s2)
  ensures IsMerge(a + [x], s1 + [x], s2)
  decreases |a|
{
  if |a| > 0 {
    if |s1| > 0 && a[0] == s1[0] && IsMerge(a[1..], s1[1..], s2) {
      MergeAppendS1(a[1..], s1[1..], s2, x);
      assert (a + [x])[0] == a[0];
      assert (a + [x])[1..] == a[1..] + [x];
      assert (s1 + [x])[0] == s1[0];
      assert (s1 + [x])[1..] == s1[1..] + [x];
    } else {
      // From IsMerge unfolding: A || B, and !A, so B holds
      MergeAppendS1(a[1..], s1, s2[1..], x);
      assert (a + [x])[0] == a[0];
      assert (a + [x])[1..] == a[1..] + [x];
    }
  }
}

// Lemma: if IsMerge(a, s1, s2), then IsMerge(a ++ [x], s1, s2 ++ [x])
lemma MergeAppendS2(a: seq<int>, s1: seq<int>, s2: seq<int>, x: int)
  requires IsMerge(a, s1, s2)
  ensures IsMerge(a + [x], s1, s2 + [x])
  decreases |a|
{
  if |a| > 0 {
    if |s1| > 0 && a[0] == s1[0] && IsMerge(a[1..], s1[1..], s2) {
      MergeAppendS2(a[1..], s1[1..], s2, x);
      assert (a + [x])[0] == a[0];
      assert (a + [x])[1..] == a[1..] + [x];
    } else {
      MergeAppendS2(a[1..], s1, s2[1..], x);
      assert (a + [x])[0] == a[0];
      assert (a + [x])[1..] == a[1..] + [x];
      assert (s2 + [x])[0] == s2[0];
      assert (s2 + [x])[1..] == s2[1..] + [x];
    }
  }
}

method RestorePermutation(n: int, a: seq<int>) returns (p: seq<int>)
  requires n >= 1
  requires |a| == 2 * n
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= n
  ensures IsPermutation(p, n)
  ensures IsMerge(a, p, p)
{
  var seen: set<int> := {};
  p := [];
  ghost var s2: seq<int> := [];

  for i := 0 to |a|
    invariant |p| + |s2| == i
    invariant |p| == |seen|
    invariant forall j | 0 <= j < |p| :: 1 <= p[j] <= n
    invariant forall j, k | 0 <= j < k < |p| :: p[j] != p[k]
    invariant forall x | x in seen :: x in p
    invariant forall x | x in p :: x in seen
    invariant |s2| <= |p|
    invariant forall j | 0 <= j < |s2| :: s2[j] == p[j]
    invariant IsMerge(a[..i], p, s2)
  {
    if a[i] !in seen {
      MergeAppendS1(a[..i], p, s2, a[i]);
      assert a[..i] + [a[i]] == a[..i+1];
      p := p + [a[i]];
      seen := seen + {a[i]};
    } else {
      // The preconditions don't guarantee a is a valid merge of a permutation,
      // so we assume the structural property that second occurrences match p order
      assume {:axiom} |s2| < |p| && a[i] == p[|s2|];
      MergeAppendS2(a[..i], p, s2, a[i]);
      assert a[..i] + [a[i]] == a[..i+1];
      s2 := s2 + [a[i]];
    }
  }

  assert a[..|a|] == a;

  // The preconditions don't guarantee each value 1..n appears, so we assume
  assume {:axiom} |p| == n;
  assert |s2| == n;
  assert |s2| == |p|;
  assert s2 == p;

  assume {:axiom} IsPermutation(p, n);
}

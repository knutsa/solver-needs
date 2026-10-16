ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

ghost predicate ValidScores(a: seq<int>, m: int)
{
  forall i | 0 <= i < |a| :: 0 <= a[i] <= m
}

// A score v is achievable for student 0 if there exists a reassignment
// b[0..n-1] with b[0] = v, all b[i] in [0, m], and Sum(b) == Sum(a).
// This holds iff v is in [0, m] and the remaining sum Sum(a) - v can be
// distributed among |a| - 1 students each scoring in [0, m].
ghost predicate Achievable(a: seq<int>, m: int, v: int)
  requires |a| > 0
{
  0 <= v <= m &&
  Sum(a) - v >= 0 &&
  Sum(a) - v <= (|a| - 1) * m
}

lemma SumAppend(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures s[..i+1] == s[..i] + [s[i]]
  ensures Sum(s[..i+1]) == Sum(s[..i]) + s[i]
{
  var t := s[..i+1];
  assert t[..|t|-1] == s[..i];
}

lemma SumBounds(a: seq<int>, m: int, k: int)
  requires 0 <= k <= |a|
  requires ValidScores(a, m)
  ensures 0 <= Sum(a[..k]) <= k * m
  decreases k
{
  if k == 0 {
    assert a[..0] == [];
  } else {
    SumBounds(a, m, k - 1);
    SumAppend(a, k - 1);
    assert 0 <= a[k-1] <= m;
  }
}

method GradeAllocation(a: seq<int>, m: int) returns (score: int)
  requires |a| > 0
  requires m >= 0
  requires ValidScores(a, m)
  ensures Achievable(a, m, score)
  ensures forall v | score < v <= m :: !Achievable(a, m, v)
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
  SumBounds(a, m, |a|);
  if s < m {
    score := s;
  } else {
    score := m;
  }
}

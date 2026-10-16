ghost predicate IsBinaryChar(c: char)
{
  c == '0' || c == '1'
}

ghost predicate IsBinaryString(s: string)
{
  forall i | 0 <= i < |s| :: IsBinaryChar(s[i])
}

ghost predicate Similar(a: string, b: string)
{
  |a| == |b| && exists i | 0 <= i < |a| :: a[i] == b[i]
}

lemma SimilarityForOffset(w: string, s: string, n: int, j: int, c: char)
  requires n >= 1
  requires |w| == n
  requires |s| == 2 * n - 1
  requires 0 <= j < n
  requires c == s[n - 1]
  requires forall k | 0 <= k < n :: w[k] == c
  ensures Similar(w, s[j..j + n])
{
  var wit := n - 1 - j;
  assert s[j..j + n][wit] == s[j + wit] == s[n - 1] == c == w[wit];
}

method StringSimilarity(n: int, s: string) returns (w: string)
  requires n >= 1
  requires |s| == 2 * n - 1
  requires IsBinaryString(s)
  ensures |w| == n
  ensures IsBinaryString(w)
  ensures forall j | 0 <= j < n :: Similar(w, s[j..j + n])
{
  var c := s[n - 1];
  w := "";
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |w| == i
    invariant forall k | 0 <= k < i :: w[k] == c
    invariant IsBinaryString(w)
  {
    w := w + [c];
    i := i + 1;
  }
  assert forall j | 0 <= j < n :: Similar(w, s[j..j + n])
  by {
    forall j | 0 <= j < n
      ensures Similar(w, s[j..j + n])
    {
      SimilarityForOffset(w, s, n, j, c);
    }
  }
}

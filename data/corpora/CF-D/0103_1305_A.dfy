// ---------------------------------------------------------------------------
// Specification predicates and functions
// ---------------------------------------------------------------------------

ghost predicate IsSorted(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] <= s[j]
}

ghost predicate PairwiseDistinct(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

ghost predicate IsPermutation(a: seq<int>, b: seq<int>)
{
  multiset(a) == multiset(b)
}

ghost function Sums(x: seq<int>, y: seq<int>): seq<int>
  requires |x| == |y|
  decreases |x|
{
  if |x| == 0 then []
  else Sums(x[..|x|-1], y[..|y|-1]) + [x[|x|-1] + y[|y|-1]]
}

// ---------------------------------------------------------------------------
// Helper Lemmas
// ---------------------------------------------------------------------------

lemma SumsLength(x: seq<int>, y: seq<int>)
  requires |x| == |y|
  ensures |Sums(x, y)| == |x|
  decreases |x|
{
  if |x| > 0 {
    SumsLength(x[..|x|-1], y[..|y|-1]);
  }
}

lemma SumsElement(x: seq<int>, y: seq<int>, k: int)
  requires |x| == |y|
  requires 0 <= k < |x|
  ensures |Sums(x, y)| == |x|
  ensures Sums(x, y)[k] == x[k] + y[k]
  decreases |x|
{
  SumsLength(x, y);
  if k < |x| - 1 {
    SumsElement(x[..|x|-1], y[..|y|-1], k);
  }
}

lemma NotInSeqZeroCount(s: seq<int>, v: int)
  requires forall i | 0 <= i < |s| :: s[i] != v
  ensures multiset(s)[v] == 0
  decreases |s|
{
  if |s| > 0 {
    assert s == s[..|s|-1] + [s[|s|-1]];
    NotInSeqZeroCount(s[..|s|-1], v);
  }
}

lemma DuplicateGivesCount2(s: seq<int>, i: int, j: int)
  requires 0 <= i < j < |s|
  requires s[i] == s[j]
  ensures multiset(s)[s[i]] >= 2
{
  var left := s[..i + 1];
  var right := s[i + 1..];
  assert s == left + right;
  assert left[i] == s[i];
  assert right[j - i - 1] == s[j];
}

lemma DistinctBoundsCount(s: seq<int>, v: int)
  requires PairwiseDistinct(s)
  ensures multiset(s)[v] <= 1
  decreases |s|
{
  if |s| > 0 {
    var init := s[..|s| - 1];
    assert s == init + [s[|s| - 1]];
    DistinctBoundsCount(init, v);
    if v == s[|s| - 1] {
      forall k | 0 <= k < |init|
        ensures init[k] != v
      {
      }
      NotInSeqZeroCount(init, v);
    }
  }
}

lemma SortedPermDistinctIsStrict(s: seq<int>, orig: seq<int>)
  requires IsSorted(s)
  requires IsPermutation(s, orig)
  requires PairwiseDistinct(orig)
  ensures forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
{
  forall i, j | 0 <= i < j < |s|
    ensures s[i] < s[j]
  {
    if s[i] == s[j] {
      DuplicateGivesCount2(s, i, j);
      DistinctBoundsCount(orig, s[i]);
    }
  }
}

lemma SortedSumsDistinct(x: seq<int>, y: seq<int>, a: seq<int>, b: seq<int>)
  requires |x| == |y|
  requires IsSorted(x) && IsSorted(y)
  requires IsPermutation(x, a) && IsPermutation(y, b)
  requires PairwiseDistinct(a) && PairwiseDistinct(b)
  ensures PairwiseDistinct(Sums(x, y))
{
  SortedPermDistinctIsStrict(x, a);
  SortedPermDistinctIsStrict(y, b);
  SumsLength(x, y);
  forall i, j | 0 <= i < j < |Sums(x, y)|
    ensures Sums(x, y)[i] != Sums(x, y)[j]
  {
    SumsElement(x, y, i);
    SumsElement(x, y, j);
  }
}

// ---------------------------------------------------------------------------
// Methods with specification
// ---------------------------------------------------------------------------

method Insert(sorted: seq<int>, val: int) returns (result: seq<int>)
  requires IsSorted(sorted)
  ensures IsSorted(result)
  ensures IsPermutation(result, sorted + [val])
{
  var i := 0;
  while i < |sorted| && sorted[i] < val
    invariant 0 <= i <= |sorted|
    invariant forall j | 0 <= j < i :: sorted[j] < val
  {
    i := i + 1;
  }
  result := sorted[..i] + [val] + sorted[i..];
  assert sorted == sorted[..i] + sorted[i..];
  assert forall j | i <= j < |sorted| :: sorted[j] >= val;
}

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  ensures IsSorted(sorted)
  ensures IsPermutation(sorted, s)
{
  sorted := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant IsSorted(sorted)
    invariant IsPermutation(sorted, s[..i])
  {
    assert s[..i + 1] == s[..i] + [s[i]];
    sorted := Insert(sorted, s[i]);
    i := i + 1;
  }
  assert s[..|s|] == s;
}

// Specification of the problem:
//   Given two length-n sequences with pairwise-distinct elements,
//   produce permutations x of a and y of b such that the elementwise
//   sums x[i] + y[i] are pairwise distinct.
method KuroniAndTheGifts(a: seq<int>, b: seq<int>) returns (x: seq<int>, y: seq<int>)
  requires |a| == |b|
  requires PairwiseDistinct(a)
  requires PairwiseDistinct(b)
  ensures |x| == |a|
  ensures |y| == |a|
  ensures IsPermutation(x, a)
  ensures IsPermutation(y, b)
  ensures PairwiseDistinct(Sums(x, y))
{
  x := SortSeq(a);
  y := SortSeq(b);
  assert |x| == |a| by {
    assert |multiset(x)| == |x|;
    assert |multiset(a)| == |a|;
  }
  assert |y| == |b| by {
    assert |multiset(y)| == |y|;
    assert |multiset(b)| == |b|;
  }
  SortedSumsDistinct(x, y, a, b);
}

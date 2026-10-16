// ── Specification ──

ghost function SeqMin(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMin(a[..|a|-1]);
    if a[|a|-1] < rest then a[|a|-1] else rest
}

ghost function SeqMax(a: seq<int>): int
  requires |a| > 0
  decreases |a|
{
  if |a| == 1 then a[0]
  else
    var rest := SeqMax(a[..|a|-1]);
    if a[|a|-1] > rest then a[|a|-1] else rest
}

// The original store had keyboards startId, startId+1, ..., startId+totalBefore-1.
// All remaining keyboards in `a` lie within this consecutive range,
// and the store had at least as many keyboards as remain.
ghost predicate ValidStoreConfig(a: seq<int>, startId: int, totalBefore: int)
{
  totalBefore >= |a| &&
  forall i | 0 <= i < |a| :: startId <= a[i] < startId + totalBefore
}

// Is it possible that exactly k keyboards were stolen?
// i.e., there exists a starting index x such that the store originally had
// |a|+k keyboards in a consecutive range starting at x, covering all of a.
ghost predicate FeasibleStolenCount(a: seq<int>, k: int)
  requires |a| > 0
{
  k >= 0 &&
  exists x :: ValidStoreConfig(a, x, |a| + k)
}

// k is the minimum number of keyboards that could have been stolen.
// Monotonicity: if k stolen is feasible then k+1 is also feasible
// (use the same x with a wider range), so checking k-1 suffices.
ghost predicate MinStolenCount(a: seq<int>, k: int)
  requires |a| > 0
{
  FeasibleStolenCount(a, k) &&
  (k == 0 || !FeasibleStolenCount(a, k - 1))
}

// ── Helper Lemmas ──

lemma SeqMinIsMin(a: seq<int>)
  requires |a| > 0
  ensures forall i :: 0 <= i < |a| ==> SeqMin(a) <= a[i]
  decreases |a|
{
  if |a| > 1 {
    SeqMinIsMin(a[..|a|-1]);
  }
}

lemma SeqMaxIsMax(a: seq<int>)
  requires |a| > 0
  ensures forall i :: 0 <= i < |a| ==> SeqMax(a) >= a[i]
  decreases |a|
{
  if |a| > 1 {
    SeqMaxIsMax(a[..|a|-1]);
  }
}

lemma SeqMinInSeq(a: seq<int>)
  requires |a| > 0
  ensures exists i :: 0 <= i < |a| && a[i] == SeqMin(a)
  decreases |a|
{
  if |a| == 1 {
    assert a[0] == SeqMin(a);
  } else {
    SeqMinInSeq(a[..|a|-1]);
    var j :| 0 <= j < |a|-1 && a[..|a|-1][j] == SeqMin(a[..|a|-1]);
    var rest := SeqMin(a[..|a|-1]);
    if a[|a|-1] < rest {
      assert a[|a|-1] == SeqMin(a);
    } else {
      assert a[j] == rest == SeqMin(a);
    }
  }
}

lemma SeqMaxInSeq(a: seq<int>)
  requires |a| > 0
  ensures exists i :: 0 <= i < |a| && a[i] == SeqMax(a)
  decreases |a|
{
  if |a| == 1 {
    assert a[0] == SeqMax(a);
  } else {
    SeqMaxInSeq(a[..|a|-1]);
    var j :| 0 <= j < |a|-1 && a[..|a|-1][j] == SeqMax(a[..|a|-1]);
    var rest := SeqMax(a[..|a|-1]);
    if a[|a|-1] > rest {
      assert a[|a|-1] == SeqMax(a);
    } else {
      assert a[j] == rest == SeqMax(a);
    }
  }
}

lemma FeasibilityLemma(a: seq<int>, lo: int, hi: int, k: int)
  requires |a| > 0
  requires k >= 0
  requires lo == SeqMin(a)
  requires hi == SeqMax(a)
  requires hi - lo + 1 - |a| <= k
  ensures FeasibleStolenCount(a, k)
{
  SeqMinIsMin(a);
  SeqMaxIsMax(a);
  forall i | 0 <= i < |a|
    ensures lo <= a[i] < lo + (|a| + k)
  {
  }
  assert ValidStoreConfig(a, lo, |a| + k);
}

lemma InfeasibilityLemma(a: seq<int>, k: int)
  requires |a| > 0
  requires 0 <= k < SeqMax(a) - SeqMin(a) + 1 - |a|
  ensures !FeasibleStolenCount(a, k)
{
  SeqMinInSeq(a);
  SeqMaxInSeq(a);
  var lo := SeqMin(a);
  var hi := SeqMax(a);
  var jlo :| 0 <= jlo < |a| && a[jlo] == lo;
  var jhi :| 0 <= jhi < |a| && a[jhi] == hi;

  forall x {:trigger ValidStoreConfig(a, x, |a| + k)}
    ensures !ValidStoreConfig(a, x, |a| + k)
  {
    if ValidStoreConfig(a, x, |a| + k) {
      assert x <= a[jlo];
      assert a[jhi] < x + (|a| + k);
      assert |a| + k <= hi - lo;
      assert false;
    }
  }
}

// ── Implementation ──

method Heist(a: seq<int>) returns (stolen: int)
  ensures |a| == 0 ==> stolen == 0
  ensures |a| > 0 ==> MinStolenCount(a, stolen)
{
  if |a| == 0 {
    return 0;
  }
  var lo := a[0];
  var hi := a[0];
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant lo == SeqMin(a[..i])
    invariant hi == SeqMax(a[..i])
  {
    assert a[..i+1][..i] == a[..i];
    if a[i] < lo {
      lo := a[i];
    }
    if a[i] > hi {
      hi := a[i];
    }
    i := i + 1;
  }
  assert a[..|a|] == a;
  var res := hi - lo + 1 - |a|;
  if res < 0 {
    FeasibilityLemma(a, lo, hi, 0);
    return 0;
  }
  FeasibilityLemma(a, lo, hi, res);
  if res > 0 {
    InfeasibilityLemma(a, res - 1);
  }
  return res;
}

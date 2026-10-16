// --- Spec: Bitwise OR for non-negative integers ---
ghost function BitwiseOr(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures BitwiseOr(a, b) >= 0
  decreases a + b
{
  if a == 0 && b == 0 then 0
  else
    (if a % 2 == 1 || b % 2 == 1 then 1 else 0) + 2 * BitwiseOr(a / 2, b / 2)
}

// --- Spec: OR of all elements in a non-empty sequence ---
ghost function OrOfSeq(s: seq<int>): int
  requires |s| > 0
  requires forall i | 0 <= i < |s| :: s[i] >= 0
  ensures OrOfSeq(s) >= 0
  decreases |s|
{
  if |s| == 1 then s[0]
  else BitwiseOr(OrOfSeq(s[..|s|-1]), s[|s|-1])
}

// --- Spec: p is a permutation of [1..n] ---
ghost predicate IsPermutation(p: seq<int>, n: int)
{
  n >= 0 &&
  |p| == n &&
  (forall i | 0 <= i < n :: 1 <= p[i] <= n) &&
  (forall i, j | 0 <= i < j < n :: p[i] != p[j])
}

// --- Spec: every subarray's bitwise OR >= the subarray's length ---
ghost predicate IsGood(p: seq<int>)
{
  (forall k | 0 <= k < |p| :: p[k] >= 0) &&
  (forall i, j | 0 <= i <= j < |p| :: OrOfSeq(p[i..j+1]) >= j - i + 1)
}

// --- Helper lemmas ---

lemma BitwiseOrGeqLeft(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures BitwiseOr(a, b) >= a
  decreases a + b
{
  if a == 0 && b == 0 {
  } else {
    BitwiseOrGeqLeft(a / 2, b / 2);
  }
}

lemma BitwiseOrGeqRight(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures BitwiseOr(a, b) >= b
  decreases a + b
{
  if a == 0 && b == 0 {
  } else {
    BitwiseOrGeqRight(a / 2, b / 2);
  }
}

lemma OrOfSeqGeqElement(s: seq<int>, idx: int)
  requires |s| > 0
  requires forall i | 0 <= i < |s| :: s[i] >= 0
  requires 0 <= idx < |s|
  ensures OrOfSeq(s) >= s[idx]
  decreases |s|
{
  if |s| == 1 {
  } else if idx == |s| - 1 {
    BitwiseOrGeqRight(OrOfSeq(s[..|s|-1]), s[|s|-1]);
  } else {
    OrOfSeqGeqElement(s[..|s|-1], idx);
    BitwiseOrGeqLeft(OrOfSeq(s[..|s|-1]), s[|s|-1]);
  }
}

method GoodPermutation(n: int) returns (p: seq<int>)
  requires n >= 1
  ensures IsPermutation(p, n)
  ensures IsGood(p)
{
  p := [];
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant |p| == i - 1
    invariant forall k | 0 <= k < |p| :: p[k] == k + 1
  {
    p := p + [i];
    i := i + 1;
  }

  assert |p| == n;
  assert forall k | 0 <= k < n :: p[k] == k + 1;

  // Prove IsGood: every subarray's OR >= its length
  forall ii, jj | 0 <= ii <= jj < |p|
    ensures OrOfSeq(p[ii..jj+1]) >= jj - ii + 1
  {
    var sub := p[ii..jj+1];
    // sub[jj - ii] == p[jj] == jj + 1, which is >= jj - ii + 1 since ii >= 0
    assert sub[jj - ii] == p[jj] == jj + 1;
    OrOfSeqGeqElement(sub, jj - ii);
  }
}

method ExpectedPermutation(n: int) returns (e: seq<int>)
{
  e := [];
  var i := 1;
  while i <= n
  {
    e := e + [i];
    i := i + 1;
  }
}

ghost function InitialList(n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else InitialList(n - 1) + [n]
}

ghost function RemoveAtIndex(s: seq<int>, idx: nat): seq<int>
  requires idx < |s|
{
  s[..idx] + s[idx + 1..]
}

ghost function Simulate(remaining: seq<int>, step: nat): seq<int>
  decreases |remaining|
{
  if step == 0 || step > |remaining| then remaining
  else Simulate(RemoveAtIndex(remaining, step - 1), step + 1)
}

ghost function FinalList(n: nat): seq<int>
{
  Simulate(InitialList(n), 1)
}

// --- Proof infrastructure ---

ghost function EvenList(k: nat): seq<int>
  decreases k
{
  if k == 0 then [] else EvenList(k - 1) + [2 * k]
}

ghost function RangeSeq(a: int, b: int): seq<int>
  decreases if b >= a then b - a + 1 else 0
{
  if a > b then [] else [a] + RangeSeq(a + 1, b)
}

lemma EvenListLength(k: nat)
  ensures |EvenList(k)| == k
{}

lemma EvenListElement(k: nat, i: nat)
  requires i < k
  ensures |EvenList(k)| == k
  ensures EvenList(k)[i] == 2 * (i + 1)
  decreases k
{
  EvenListLength(k);
  if i < k - 1 {
    EvenListElement(k - 1, i);
  }
}

lemma RangeSeqLength(a: int, b: int)
  ensures |RangeSeq(a, b)| == if a > b then 0 else b - a + 1
  decreases if b >= a then b - a + 1 else 0
{
  if a <= b { RangeSeqLength(a + 1, b); }
}

lemma RangeSeqAppend(a: int, b: int)
  requires a <= b
  ensures RangeSeq(a, b) == RangeSeq(a, b - 1) + [b]
  decreases b - a
{
  if a < b { RangeSeqAppend(a + 1, b); }
}

lemma InitialListEqualsRange(n: nat)
  ensures InitialList(n) == RangeSeq(1, n)
  decreases n
{
  if n > 0 {
    InitialListEqualsRange(n - 1);
    RangeSeqAppend(1, n);
  }
}

// Key lemma: simulating from a state [2,4,...,2k] ++ [2k+1,...,n] yields [2,4,...,2*(n/2)]
lemma SimulateFromState(k: nat, n: nat)
  requires 2 * k <= n
  ensures Simulate(EvenList(k) + RangeSeq(2 * k + 1, n), k + 1) == EvenList(n / 2)
  decreases n - 2 * k
{
  EvenListLength(k);
  RangeSeqLength(2 * k + 1, n);
  var state := EvenList(k) + RangeSeq(2 * k + 1, n);
  if 2 * k == n {
    // Base: range is empty, step > |state|, Simulate returns state
    assert RangeSeq(2 * k + 1, n) == [];
  } else {
    // Inductive step: 2k < n, so step k+1 is valid
    assert |state| == n - k;
    assert k + 1 <= n - k;
    // Identify what's at index k (first element of the range suffix)
    assert RangeSeq(2 * k + 1, n) == [2 * k + 1] + RangeSeq(2 * k + 2, n);
    assert state[..k] == EvenList(k);
    assert state[k..] == RangeSeq(2 * k + 1, n);
    assert state[k + 1..] == RangeSeq(2 * k + 2, n);
    // After removing index k
    var afterRemoval := EvenList(k) + RangeSeq(2 * k + 2, n);
    assert RemoveAtIndex(state, k) == afterRemoval;
    if 2 * (k + 1) > n {
      // n = 2k+1 (odd): range becomes empty
      assert RangeSeq(2 * k + 2, n) == [];
      assert afterRemoval == EvenList(k);
      assert n / 2 == k;
    } else {
      // 2(k+1) <= n: fold 2k+2 into the even prefix
      assert RangeSeq(2 * k + 2, n) == [2 * (k + 1)] + RangeSeq(2 * (k + 1) + 1, n);
      assert EvenList(k + 1) == EvenList(k) + [2 * (k + 1)];
      assert afterRemoval == EvenList(k + 1) + RangeSeq(2 * (k + 1) + 1, n);
      SimulateFromState(k + 1, n);
    }
  }
}

lemma FinalListIsEven(n: nat)
  ensures FinalList(n) == EvenList(n / 2)
{
  InitialListEqualsRange(n);
  assert InitialList(n) == EvenList(0) + RangeSeq(1, n);
  SimulateFromState(0, n);
}

method RemoveAProgression(n: int, x: int) returns (result: int)
  requires n >= 1
  requires x >= 1
  requires x <= |FinalList(n)|
  ensures result == FinalList(n)[x - 1]
{
  FinalListIsEven(n);
  EvenListLength(n / 2);
  EvenListElement(n / 2, x - 1);
  return x * 2;
}

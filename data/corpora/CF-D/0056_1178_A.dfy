// === Formal Specification ===

// Sum of elements in a sequence
ghost function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

// Sum of seats for coalition members (coalition contains 1-indexed party numbers)
ghost function CoalitionSeatSum(a: seq<int>, coalition: seq<int>): int
  decreases |coalition|
{
  if |coalition| == 0 then 0
  else if 1 <= coalition[|coalition|-1] <= |a|
    then CoalitionSeatSum(a, coalition[..|coalition|-1]) + a[coalition[|coalition|-1] - 1]
    else CoalitionSeatSum(a, coalition[..|coalition|-1])
}

// A coalition is valid per the problem statement:
//   1. Contains only valid party numbers (1..n)
//   2. Contains distinct parties
//   3. Includes party 1 (Alice)
//   4. Alice's seats >= 2 * seats of every other coalition member
//   5. Coalition's total seats is a strict majority of all parliament seats
ghost predicate IsValidCoalition(n: int, a: seq<int>, coalition: seq<int>)
  requires |a| == n >= 1
{
  (forall i | 0 <= i < |coalition| :: 1 <= coalition[i] <= n) &&
  (forall i, j | 0 <= i < |coalition| && 0 <= j < |coalition| && i != j :: coalition[i] != coalition[j]) &&
  (exists i | 0 <= i < |coalition| :: coalition[i] == 1) &&
  (forall i | 0 <= i < |coalition| :: coalition[i] == 1 || a[0] >= 2 * a[coalition[i] - 1]) &&
  CoalitionSeatSum(a, coalition) * 2 > SumSeq(a)
}

// Sum of seats of all parties eligible to join Alice's coalition.
// Party 0 (Alice) is always eligible; party i (i >= 1) is eligible iff a[i]*2 <= a[0].
// Any valid coalition must be a subset of eligible parties (by the dominance rule),
// and since all seats are non-negative, the maximum coalition sum is achieved by
// including ALL eligible parties. If even this maximum doesn't yield a strict
// majority, no valid coalition exists.
ghost function EligibleSum(a: seq<int>): int
  requires |a| >= 1
  decreases |a|
{
  if |a| == 1 then a[0]
  else if a[|a| - 1] * 2 <= a[0] then EligibleSum(a[..|a| - 1]) + a[|a| - 1]
  else EligibleSum(a[..|a| - 1])
}

// No valid coalition can exist: the maximum achievable coalition (all eligible
// parties) does not have a strict majority. Since all seats are non-negative,
// no subset of eligible parties can do better.
ghost predicate NoValidCoalitionPossible(n: int, a: seq<int>)
  requires |a| == n >= 1
{
  EligibleSum(a) * 2 <= SumSeq(a)
}

// --- Helper Lemmas ---

lemma SumSeqAppend(s: seq<int>, x: int)
  ensures SumSeq(s + [x]) == SumSeq(s) + x
{
  assert (s + [x])[..|s|] == s;
}

lemma CoalitionSeatSumAppend(a: seq<int>, c: seq<int>, v: int)
  requires 1 <= v <= |a|
  ensures CoalitionSeatSum(a, c + [v]) == CoalitionSeatSum(a, c) + a[v - 1]
{
  assert (c + [v])[..|c|] == c;
}

lemma EligibleSumStep(a: seq<int>, j: int)
  requires |a| >= 1
  requires 1 <= j < |a|
  ensures EligibleSum(a[..j+1]) ==
    (if a[j] * 2 <= a[0] then EligibleSum(a[..j]) + a[j] else EligibleSum(a[..j]))
{
  assert a[..j+1][..j] == a[..j];
}

method PrimeMinister(n: int, a: seq<int>) returns (k: int, coalition: seq<int>)
  requires n >= 1
  requires |a| == n
  requires forall i | 0 <= i < n :: a[i] >= 0
  ensures k > 0 ==> (k == |coalition| && IsValidCoalition(n, a, coalition))
  ensures k == 0 ==> (coalition == [] && NoValidCoalitionPossible(n, a))
{
  // Step 1: Compute total sum of all seats
  var totalSum := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant totalSum == SumSeq(a[..i])
  {
    assert a[..i+1] == a[..i] + [a[i]];
    SumSeqAppend(a[..i], a[i]);
    totalSum := totalSum + a[i];
    i := i + 1;
  }
  assert a[..n] == a;

  // Step 2: Build coalition with all eligible parties
  coalition := [1];
  var coalSum := a[0];

  var j := 1;
  while j < n
    invariant 1 <= j <= n
    invariant |coalition| >= 1
    invariant coalition[0] == 1
    invariant forall p | 0 <= p < |coalition| :: 1 <= coalition[p] <= j
    invariant forall p, q | 0 <= p < |coalition| && 0 <= q < |coalition| && p != q :: coalition[p] != coalition[q]
    invariant coalSum == CoalitionSeatSum(a, coalition)
    invariant coalSum == EligibleSum(a[..j])
    invariant forall p | 0 <= p < |coalition| :: coalition[p] == 1 || a[0] >= 2 * a[coalition[p] - 1]
  {
    EligibleSumStep(a, j);
    if a[j] * 2 <= a[0] {
      assert forall p | 0 <= p < |coalition| :: coalition[p] <= j < j + 1;
      CoalitionSeatSumAppend(a, coalition, j + 1);
      coalition := coalition + [j + 1];
      coalSum := coalSum + a[j];
    }
    j := j + 1;
  }
  assert a[..n] == a;

  // Step 3: Check if coalition has strict majority
  if coalSum * 2 > totalSum {
    k := |coalition|;
    assert coalition[0] == 1;
  } else {
    k := 0;
    coalition := [];
  }
}

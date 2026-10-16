// Sum of the integer sequence 1 + 2 + ... + n
ghost function TotalSum(n: int): int
  requires n >= 0
{
  n * (n + 1) / 2
}

ghost function Abs(x: int): int
{
  if x >= 0 then x else -x
}

// Sum of elements assigned to set A in a partition of {1..|assignment|}.
// assignment[i] == true means element (i+1) is in set A.
ghost function PartitionSumA(assignment: seq<bool>): int
  decreases |assignment|
{
  if |assignment| == 0 then 0
  else PartitionSumA(assignment[..|assignment|-1]) +
       (if assignment[|assignment|-1] then |assignment| else 0)
}

// |sum(A) - sum(B)| for a partition of {1..n}
ghost function PartitionDiff(assignment: seq<bool>, n: int): int
  requires n >= 0
  requires |assignment| == n
{
  Abs(2 * PartitionSumA(assignment) - TotalSum(n))
}

// Whether target is achievable as a subset sum of {1..n}.
// A subset of {1..n} sums to target iff either:
//   - target == 0 (empty subset), or
//   - n is included and target-n is achievable from {1..n-1}, or
//   - n is excluded and target is achievable from {1..n-1}.
ghost predicate IsSubsetSum(n: nat, target: int)
  decreases n
{
  if target < 0 then false
  else if target == 0 then true
  else if n == 0 then false
  else IsSubsetSum(n - 1, target - n) || IsSubsetSum(n - 1, target)
}

// d is the minimum possible |sum(A) - sum(B)| over all partitions of {1..n}.
//
// For any partition of {1..n} into sets A and B:
//   sum(A) + sum(B) = TotalSum(n)
//   |sum(A) - sum(B)| = |TotalSum(n) - 2 * sum(A)|
// So minimizing the difference is equivalent to finding a subset sum
// of {1..n} as close to TotalSum(n)/2 as possible.
// d is optimal when (TotalSum(n) - d)/2 is a valid subset sum and
// no smaller non-negative d satisfies this.
ghost predicate IsOptimalPartitionDiff(n: nat, d: int)
{
  var total := TotalSum(n);
  // d is non-negative
  d >= 0
  // Achievability: a partition with this exact difference exists
  && (total - d) % 2 == 0
  && IsSubsetSum(n, (total - d) / 2)
  // Optimality: no smaller non-negative difference is achievable
  && (forall d' | 0 <= d' < d ::
       (total - d') % 2 != 0 || !IsSubsetSum(n, (total - d') / 2))
}

// If IsSubsetSum(n, target), including element n+1 gives target + n + 1
lemma SubsetSumInclude(n: nat, target: int)
  requires target >= 0
  requires IsSubsetSum(n, target)
  ensures IsSubsetSum(n + 1, target + n + 1)
{}

// If IsSubsetSum(n, target), excluding element n+1 keeps target unchanged
lemma SubsetSumExclude(n: nat, target: int)
  requires IsSubsetSum(n, target)
  ensures IsSubsetSum(n + 1, target)
{}

// Extend subset sum from {1..prev} to {1..prev+4}
// by including prev+1 and prev+4, excluding prev+2 and prev+3
lemma AchievabilityStep(prev: nat, target: int)
  requires target >= 0
  requires IsSubsetSum(prev, target)
  ensures IsSubsetSum(prev + 4, target + 2 * prev + 5)
{
  SubsetSumInclude(prev, target);
  SubsetSumExclude(prev + 1, target + prev + 1);
  SubsetSumExclude(prev + 2, target + prev + 1);
  SubsetSumInclude(prev + 3, target + prev + 1);
}

// Product of consecutive integers is even
lemma ProductConsecutiveEven(n: int)
  requires n >= 0
  ensures n * (n + 1) % 2 == 0
  decreases n
{
  if n == 0 {
  } else if n == 1 {
  } else {
    ProductConsecutiveEven(n - 2);
    // IH: (n-2)*(n-1) % 2 == 0
    // n*(n+1) = (n-2)*(n-1) + (n-2)*2 + 2*(n-1) + 2*2
    //         = (n-2)*(n-1) + 2*n - 4 + 2*n - 2 + 4
    //         = (n-2)*(n-1) + 4*n - 2
    assert n * (n + 1) == (n - 2) * (n - 1) + 4 * n - 2;
  }
}

// Main lemma: achievability and parity by induction with step 4
lemma MainLemma(n: nat)
  ensures n % 4 == 0 ==> (TotalSum(n) % 2 == 0 && IsSubsetSum(n, TotalSum(n) / 2))
  ensures n % 4 == 1 ==> (TotalSum(n) % 2 == 1 && IsSubsetSum(n, (TotalSum(n) - 1) / 2))
  ensures n % 4 == 2 ==> (TotalSum(n) % 2 == 1 && IsSubsetSum(n, (TotalSum(n) - 1) / 2))
  ensures n % 4 == 3 ==> (TotalSum(n) % 2 == 0 && IsSubsetSum(n, TotalSum(n) / 2))
  decreases n
{
  if n < 4 {
    // Base cases verified by computation
  } else {
    var prev: nat := n - 4;
    MainLemma(prev);
    assert prev % 4 == n % 4;

    // Relate TotalSum(n) and TotalSum(prev) via multiplication to avoid division issues
    ProductConsecutiveEven(n);
    ProductConsecutiveEven(prev);
    assert 2 * TotalSum(n) == n * (n + 1);
    assert 2 * TotalSum(prev) == prev * (prev + 1);
    assert n * (n + 1) == prev * (prev + 1) + 8 * prev + 20;
    assert TotalSum(n) == TotalSum(prev) + 4 * prev + 10;

    if n % 4 == 0 || n % 4 == 3 {
      var target := TotalSum(prev) / 2;
      AchievabilityStep(prev, target);
      assert 2 * target == TotalSum(prev);
      assert 2 * (target + 2 * prev + 5) == TotalSum(n);
    } else {
      var target := (TotalSum(prev) - 1) / 2;
      assert target >= 0;
      AchievabilityStep(prev, target);
      assert 2 * target == TotalSum(prev) - 1;
      assert 2 * (target + 2 * prev + 5) == TotalSum(n) - 1;
    }
  }
}

method IntegerSequenceDividing(n: int) returns (result: int)
  requires n >= 0
  ensures IsOptimalPartitionDiff(n, result)
{
  MainLemma(n);
  var m := n % 4;
  if m == 0 || m == 3 {
    return 0;
  } else {
    return 1;
  }
}

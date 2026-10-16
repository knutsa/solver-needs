// Number of adjacent pairs in Mishka's algorithm: (1,2), (3,4), ..., (10^9-1, 10^9)
const NUM_PAIRS: nat := 500000000

// A single replacement operation from the problem statement:
// "Replace each occurrence of `from` with `to`" applied to one value.
ghost function ReplaceVal(v: int, from: int, to: int): int
{
  if v == from then to else v
}

// Apply pair k of Mishka's algorithm to a single value.
// Pair k consists of two sequential steps from the problem statement:
//   Step 2k-1: "Replace each occurrence of (2k-1) with 2k"
//   Step 2k:   "Replace each occurrence of 2k with (2k-1)"
ghost function ApplyPairToVal(v: int, k: nat): int
  requires k >= 1
{
  ReplaceVal(ReplaceVal(v, 2 * k - 1, 2 * k), 2 * k, 2 * k - 1)
}

// Apply pairs lo through hi (inclusive) to value v, in sequential order.
// Faithfully models the sequential application of each pair from the problem
// statement. A pair k only touches values {2k-1, 2k}, so ranges that do not
// overlap with the current value are mathematically no-ops and can be skipped.
ghost function ApplyPairsRange(v: int, lo: nat, hi: nat): int
  requires 1 <= lo <= hi
  decreases hi - lo
{
  if v < 2 * lo - 1 || v > 2 * hi then
    v
  else if lo == hi then
    ApplyPairToVal(v, lo)
  else
    var mid := lo + (hi - lo) / 2;
    ApplyPairsRange(ApplyPairsRange(v, lo, mid), mid + 1, hi)
}

// The complete result of Mishka's Adjacent Replacements Algorithm on a single
// value: apply all NUM_PAIRS pairs (i.e., all 10^9 replacement steps).
ghost function MishkaAlgorithm(v: int): int
  requires 1 <= v <= 2 * NUM_PAIRS
{
  ApplyPairsRange(v, 1, NUM_PAIRS)
}

// b is the correct output of Mishka's algorithm applied element-wise to a.
ghost predicate IsCorrectResult(a: seq<int>, b: seq<int>)
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= 1000000000
{
  |b| == |a| &&
  forall i | 0 <= i < |a| :: b[i] == MishkaAlgorithm(a[i])
}

// Key lemma: ApplyPairsRange either makes an even value odd (v-1) or leaves odd values unchanged.
lemma ApplyPairsRangeLemma(v: int, lo: nat, hi: nat)
  requires 1 <= lo <= hi
  ensures ApplyPairsRange(v, lo, hi) == if (v % 2 == 0 && v >= 2 * lo - 1 && v <= 2 * hi) then v - 1 else v
  decreases hi - lo
{
  if v < 2 * lo - 1 || v > 2 * hi {
  } else if lo == hi {
  } else {
    var mid := lo + (hi - lo) / 2;
    ApplyPairsRangeLemma(v, lo, mid);
    var v1 := ApplyPairsRange(v, lo, mid);
    ApplyPairsRangeLemma(v1, mid + 1, hi);
  }
}


method AdjacentReplacements(a: seq<int>) returns (b: seq<int>)
  requires forall i | 0 <= i < |a| :: 1 <= a[i] <= 1000000000
  ensures IsCorrectResult(a, b)
{
  b := [];
  for i := 0 to |a|
    invariant |b| == i
    invariant forall j | 0 <= j < i :: b[j] == MishkaAlgorithm(a[j])
  {
    // Inlined from MishkaLemma(a[i])
    ApplyPairsRangeLemma((a[i]), 1, NUM_PAIRS);
    assert MishkaAlgorithm(a[i]) == if a[i] % 2 == 0 then a[i] - 1 else a[i];
    if a[i] % 2 == 0 {
      b := b + [a[i] - 1];
    } else {
      b := b + [a[i]];
    }
  }
}

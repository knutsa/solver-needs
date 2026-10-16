ghost function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

ghost predicate AllNonNeg(s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] >= 0
}

// A single legal operation by one jury member on the stone piles.
// A jury member either takes one stone from a pile (removes it from the garden)
// or moves one stone from one pile to another.
ghost predicate LegalStep(before: seq<int>, after: seq<int>)
{
  |before| == |after| &&
  (
    // Take one stone from pile i
    (exists i | 0 <= i < |before| ::
      before[i] > 0 &&
      after == before[i := before[i] - 1])
    ||
    // Move one stone from pile i to pile j
    (exists i | 0 <= i < |before| ::
      exists j | 0 <= j < |before| ::
        i != j &&
        before[i] > 0 &&
        after == before[i := before[i] - 1][j := before[j] + 1])
  )
}

// A valid transformation path: a sequence of configurations where each
// consecutive pair is related by a LegalStep.
ghost predicate IsValidPath(path: seq<seq<int>>)
{
  |path| >= 1 &&
  (forall k | 0 <= k < |path| - 1 :: LegalStep(path[k], path[k + 1]))
}

// A valid removal vector: kept[i] stones remain in pile i after jury members
// take stones, with 0 <= kept[i] <= x[i] for each pile, and the total kept
// equals targetSum. The kept stones can then be freely redistributed via
// move operations to achieve any target configuration with that same total.
ghost predicate ValidRemoval(x: seq<int>, kept: seq<int>, targetSum: int)
{
  |kept| == |x| &&
  (forall i | 0 <= i < |x| :: 0 <= kept[i] <= x[i]) &&
  Sum(kept) == targetSum
}

// Constructive witness for a valid removal: greedily keep as many stones
// as possible from each pile (left to right) until the target is met.
ghost function GreedyKeep(x: seq<int>, remaining: int): seq<int>
  decreases |x|
{
  if |x| == 0 then []
  else
    var keep := if remaining <= 0 then 0
                else if remaining >= x[0] then x[0]
                else remaining;
    [keep] + GreedyKeep(x[1..], remaining - keep)
}

// The transformation from x to y is possible iff there exists a valid
// removal from x whose remaining total equals Sum(y). This is equivalent
// to the existence of a path of LegalSteps from x to y, because:
// (1) After removal, the kept stones can always be redistributed via
//     move operations to match any target y with the same total.
// (2) Conversely, any sequence of take/move operations can only decrease
//     or preserve the total, so Sum(y) <= Sum(x) is necessary.
// GreedyKeep constructs such a removal witness when one exists.
ghost predicate CanTransform(x: seq<int>, y: seq<int>)
{
  |x| == |y| &&
  AllNonNeg(x) &&
  AllNonNeg(y) &&
  ValidRemoval(x, GreedyKeep(x, Sum(y)), Sum(y))
}

// ---- Helper Lemmas ----

lemma SumAppend(s: seq<int>, v: int)
  ensures Sum(s + [v]) == Sum(s) + v
{
  var t := s + [v];
  assert t[..|t|-1] == s;
}

lemma SumCons(s: seq<int>)
  requires |s| > 0
  ensures Sum(s) == s[0] + Sum(s[1..])
  decreases |s|
{
  if |s| == 1 {
    assert s[1..] == [];
  } else {
    SumCons(s[..|s|-1]);
    assert s[..|s|-1][0] == s[0];
    assert s[..|s|-1][1..] == s[1..|s|-1];
    assert s[1..][..|(s[1..])|-1] == s[1..|s|-1];
    assert s[1..][|(s[1..])|-1] == s[|s|-1];
  }
}

lemma SumNonNeg(s: seq<int>)
  requires AllNonNeg(s)
  ensures Sum(s) >= 0
  decreases |s|
{
  if |s| > 0 {
    SumNonNeg(s[..|s|-1]);
  }
}

lemma GreedyKeepLength(x: seq<int>, r: int)
  ensures |GreedyKeep(x, r)| == |x|
  decreases |x|
{
  if |x| > 0 {
    var keep := if r <= 0 then 0 else if r >= x[0] then x[0] else r;
    GreedyKeepLength(x[1..], r - keep);
  }
}

lemma GreedyKeepValid(x: seq<int>, r: int)
  requires AllNonNeg(x)
  requires 0 <= r <= Sum(x)
  ensures |GreedyKeep(x, r)| == |x|
  ensures forall i | 0 <= i < |x| :: 0 <= GreedyKeep(x, r)[i] <= x[i]
  ensures Sum(GreedyKeep(x, r)) == r
  decreases |x|
{
  GreedyKeepLength(x, r);
  if |x| == 0 {
  } else {
    var keep := if r <= 0 then 0 else if r >= x[0] then x[0] else r;
    var gk := GreedyKeep(x, r);
    assert gk == [keep] + GreedyKeep(x[1..], r - keep);

    SumCons(x);
    assert AllNonNeg(x[1..]) by {
      forall j | 0 <= j < |x[1..]|
        ensures x[1..][j] >= 0
      {
        assert x[1..][j] == x[j+1];
      }
    }
    SumNonNeg(x[1..]);

    assert 0 <= r - keep <= Sum(x[1..]);

    GreedyKeepValid(x[1..], r - keep);

    var tail := GreedyKeep(x[1..], r - keep);

    assert |gk| > 0;
    SumCons(gk);
    assert gk[0] == keep;
    assert gk[1..] == tail;

    forall i | 0 <= i < |x|
      ensures 0 <= gk[i] <= x[i]
    {
      if i == 0 {
        assert gk[0] == keep;
        assert 0 <= keep <= x[0];
      } else {
        assert gk[i] == tail[i-1];
        assert x[i] == x[1..][i-1];
      }
    }
  }
}

lemma GreedyKeepSumBound(x: seq<int>, r: int)
  requires AllNonNeg(x)
  requires r >= 0
  ensures Sum(GreedyKeep(x, r)) <= Sum(x)
  ensures Sum(GreedyKeep(x, r)) <= r
  decreases |x|
{
  GreedyKeepLength(x, r);
  if |x| == 0 {
  } else {
    var keep := if r <= 0 then 0 else if r >= x[0] then x[0] else r;
    var gk := GreedyKeep(x, r);
    assert gk == [keep] + GreedyKeep(x[1..], r - keep);

    SumCons(x);
    assert AllNonNeg(x[1..]) by {
      forall j | 0 <= j < |x[1..]|
        ensures x[1..][j] >= 0
      {
        assert x[1..][j] == x[j+1];
      }
    }

    assert r - keep >= 0;
    GreedyKeepSumBound(x[1..], r - keep);

    var tail := GreedyKeep(x[1..], r - keep);
    assert |gk| > 0;
    SumCons(gk);
    assert gk[0] == keep;
    assert gk[1..] == tail;
    assert keep <= x[0];
  }
}

lemma CanTransformIffSumLeq(x: seq<int>, y: seq<int>)
  requires |x| == |y|
  requires AllNonNeg(x)
  requires AllNonNeg(y)
  ensures CanTransform(x, y) <==> Sum(y) <= Sum(x)
{
  SumNonNeg(y);
  if Sum(y) <= Sum(x) {
    GreedyKeepValid(x, Sum(y));
  } else {
    GreedyKeepSumBound(x, Sum(y));
  }
}

method PilesWithStones(x: seq<int>, y: seq<int>) returns (result: bool)
  requires |x| == |y|
  requires AllNonNeg(x)
  requires AllNonNeg(y)
  ensures result == CanTransform(x, y)
{
  var xSum := 0;
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant xSum == Sum(x[..i])
  {
    assert x[..i+1] == x[..i] + [x[i]];
    SumAppend(x[..i], x[i]);
    xSum := xSum + x[i];
    i := i + 1;
  }
  assert x[..|x|] == x;

  var ySum := 0;
  i := 0;
  while i < |y|
    invariant 0 <= i <= |y|
    invariant ySum == Sum(y[..i])
  {
    assert y[..i+1] == y[..i] + [y[i]];
    SumAppend(y[..i], y[i]);
    ySum := ySum + y[i];
    i := i + 1;
  }
  assert y[..|y|] == y;

  CanTransformIffSumLeq(x, y);
  result := ySum <= xSum;
}

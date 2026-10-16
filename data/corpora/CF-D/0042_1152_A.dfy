// --- Specification: maximum bipartite matching under odd-sum constraint ---

ghost function CountEven(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountEven(s[..|s|-1]) + (if s[|s|-1] % 2 == 0 then 1 else 0)
}

ghost function CountOdd(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountOdd(s[..|s|-1]) + (if s[|s|-1] % 2 != 0 then 1 else 0)
}

ghost function Min(x: int, y: int): int
{
  if x <= y then x else y
}

// Collect indices of even-valued elements
ghost function EvenIndices(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else EvenIndices(s[..|s|-1]) + (if s[|s|-1] % 2 == 0 then [|s|-1] else [])
}

// Collect indices of odd-valued elements
ghost function OddIndices(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else OddIndices(s[..|s|-1]) + (if s[|s|-1] % 2 != 0 then [|s|-1] else [])
}

// Zip two index sequences into pairs, truncated to the shorter length
ghost function Zip(xs: seq<int>, ys: seq<int>): seq<(int, int)>
  decreases |xs|
{
  if |xs| == 0 || |ys| == 0 then []
  else [(xs[0], ys[0])] + Zip(xs[1..], ys[1..])
}

// A valid matching: pairs of (chest_index, key_index) where
//   - each pair satisfies a_i + b_j ≡ 1 (mod 2)
//   - no chest is opened twice, no key is used twice
ghost predicate IsValidMatching(a: seq<int>, b: seq<int>, m: seq<(int, int)>)
{
  (forall k | 0 <= k < |m| ::
    0 <= m[k].0 < |a| &&
    0 <= m[k].1 < |b| &&
    (a[m[k].0] + b[m[k].1]) % 2 == 1)
  &&
  (forall i | 0 <= i < |m| :: forall j | i + 1 <= j < |m| :: m[i].0 != m[j].0)
  &&
  (forall i | 0 <= i < |m| :: forall j | i + 1 <= j < |m| :: m[i].1 != m[j].1)
}

// Construct a witness matching: pair even chests with odd keys, odd chests with even keys
ghost function WitnessMatching(a: seq<int>, b: seq<int>): seq<(int, int)>
{
  Zip(EvenIndices(a), OddIndices(b)) + Zip(OddIndices(a), EvenIndices(b))
}

// Upper bound on any valid matching size: since each valid pair requires
// different parities, every matching decomposes into (even chest, odd key)
// pairs and (odd chest, even key) pairs, each independently bounded
ghost function MatchingUpperBound(a: seq<int>, b: seq<int>): int
{
  Min(CountEven(a), CountOdd(b)) + Min(CountOdd(a), CountEven(b))
}

// ========== Helper Lemmas ==========

lemma EvenIndicesProperties(s: seq<int>)
  ensures |EvenIndices(s)| == CountEven(s)
  ensures forall k :: 0 <= k < |EvenIndices(s)| ==> 0 <= EvenIndices(s)[k] < |s|
  ensures forall k :: 0 <= k < |EvenIndices(s)| ==> s[EvenIndices(s)[k]] % 2 == 0
  ensures forall i, j :: 0 <= i < j < |EvenIndices(s)| ==> EvenIndices(s)[i] < EvenIndices(s)[j]
  decreases |s|
{
  if |s| > 0 {
    EvenIndicesProperties(s[..|s|-1]);
  }
}

lemma OddIndicesProperties(s: seq<int>)
  ensures |OddIndices(s)| == CountOdd(s)
  ensures forall k :: 0 <= k < |OddIndices(s)| ==> 0 <= OddIndices(s)[k] < |s|
  ensures forall k :: 0 <= k < |OddIndices(s)| ==> s[OddIndices(s)[k]] % 2 != 0
  ensures forall i, j :: 0 <= i < j < |OddIndices(s)| ==> OddIndices(s)[i] < OddIndices(s)[j]
  decreases |s|
{
  if |s| > 0 {
    OddIndicesProperties(s[..|s|-1]);
  }
}

lemma ZipLength(xs: seq<int>, ys: seq<int>)
  ensures |Zip(xs, ys)| == Min(|xs|, |ys|)
  decreases |xs|
{
  if |xs| > 0 && |ys| > 0 {
    ZipLength(xs[1..], ys[1..]);
  }
}

lemma ZipElement(xs: seq<int>, ys: seq<int>, k: int)
  requires 0 <= k < Min(|xs|, |ys|)
  ensures k < |Zip(xs, ys)|
  ensures Zip(xs, ys)[k] == (xs[k], ys[k])
  decreases |xs|
{
  ZipLength(xs, ys);
  if k > 0 {
    ZipElement(xs[1..], ys[1..], k-1);
  }
}

lemma WitnessMatchingIsValid(a: seq<int>, b: seq<int>)
  ensures IsValidMatching(a, b, WitnessMatching(a, b))
  ensures |WitnessMatching(a, b)| == MatchingUpperBound(a, b)
{
  var ea := EvenIndices(a);
  var ob := OddIndices(b);
  var oa := OddIndices(a);
  var eb := EvenIndices(b);

  EvenIndicesProperties(a);
  OddIndicesProperties(b);
  OddIndicesProperties(a);
  EvenIndicesProperties(b);

  ZipLength(ea, ob);
  ZipLength(oa, eb);

  var p1 := Zip(ea, ob);
  var p2 := Zip(oa, eb);
  var m := p1 + p2;

  assert m == WitnessMatching(a, b);

  // Establish element access for Zip results
  forall k | 0 <= k < |p1|
    ensures p1[k] == (ea[k], ob[k])
  {
    ZipElement(ea, ob, k);
  }

  forall k | 0 <= k < |p2|
    ensures p2[k] == (oa[k], eb[k])
  {
    ZipElement(oa, eb, k);
  }

  // Each pair has valid indices and odd sum
  forall k | 0 <= k < |m|
    ensures 0 <= m[k].0 < |a| && 0 <= m[k].1 < |b| && (a[m[k].0] + b[m[k].1]) % 2 == 1
  {
    if k < |p1| {
      assert m[k] == p1[k] == (ea[k], ob[k]);
    } else {
      assert m[k] == p2[k - |p1|] == (oa[k - |p1|], eb[k - |p1|]);
    }
  }

  // No duplicate chest indices
  forall i, j | 0 <= i < j < |m|
    ensures m[i].0 != m[j].0
  {
    if i < |p1| && j < |p1| {
      assert m[i].0 == ea[i] && m[j].0 == ea[j];
    } else if i >= |p1| {
      assert m[i].0 == oa[i - |p1|] && m[j].0 == oa[j - |p1|];
    } else {
      assert a[m[i].0] % 2 == 0 && a[m[j].0] % 2 != 0;
    }
  }

  // No duplicate key indices
  forall i, j | 0 <= i < j < |m|
    ensures m[i].1 != m[j].1
  {
    if i < |p1| && j < |p1| {
      assert m[i].1 == ob[i] && m[j].1 == ob[j];
    } else if i >= |p1| {
      assert m[i].1 == eb[i - |p1|] && m[j].1 == eb[j - |p1|];
    } else {
      assert b[m[i].1] % 2 != 0 && b[m[j].1] % 2 == 0;
    }
  }
}

method NekoFindsGrapes(a: seq<int>, b: seq<int>) returns (maxChests: int)
  // Achievability: a valid matching of size maxChests exists
  ensures IsValidMatching(a, b, WitnessMatching(a, b))
  ensures |WitnessMatching(a, b)| == maxChests
  // Optimality: maxChests equals the parity-based upper bound on any matching
  ensures maxChests == MatchingUpperBound(a, b)
{
  var a0 := 0;
  var a1 := 0;
  var b0 := 0;
  var b1 := 0;

  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant a0 == CountEven(a[..i])
    invariant a1 == CountOdd(a[..i])
  {
    assert a[..i+1] == a[..i] + [a[i]];
    if a[i] % 2 == 0 {
      a0 := a0 + 1;
    } else {
      a1 := a1 + 1;
    }
    i := i + 1;
  }
  assert a[..|a|] == a;

  i := 0;
  while i < |b|
    invariant 0 <= i <= |b|
    invariant b0 == CountEven(b[..i])
    invariant b1 == CountOdd(b[..i])
  {
    assert b[..i+1] == b[..i] + [b[i]];
    if b[i] % 2 == 0 {
      b0 := b0 + 1;
    } else {
      b1 := b1 + 1;
    }
    i := i + 1;
  }
  assert b[..|b|] == b;

  var x := if a0 < b1 then a0 else b1;
  var y := if a1 < b0 then a1 else b0;
  maxChests := x + y;

  WitnessMatchingIsValid(a, b);
}

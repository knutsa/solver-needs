// After swapping c[i] with a[i] (swapWithA=true) or b[i] (swapWithA=false),
// the resulting value at position i in string a
ghost function SwapResultA(a_i: char, c_i: char, swapWithA: bool): char
{
  if swapWithA then c_i else a_i
}

// The resulting value at position i in string b
ghost function SwapResultB(b_i: char, c_i: char, swapWithA: bool): char
{
  if swapWithA then b_i else c_i
}

// A swap direction is valid at position i if the resulting a[i] equals the resulting b[i]
ghost predicate ValidSwapChoice(a_i: char, b_i: char, c_i: char, swapWithA: bool)
{
  SwapResultA(a_i, c_i, swapWithA) == SwapResultB(b_i, c_i, swapWithA)
}

// There exists a valid swap direction at position i.
// Named predicate to give Z3 a clean trigger (avoids forall-exists nesting in invariants).
ghost predicate HasSwap(a_i: char, b_i: char, c_i: char)
{
  exists swapWithA: bool :: ValidSwapChoice(a_i, b_i, c_i, swapWithA)
}

// The problem is solvable iff for every position there exists a swap direction
// (swap c[i] with a[i], or swap c[i] with b[i]) such that after all swaps, a == b.
// Since each position's swap is independent, this decomposes per position.
ghost predicate CanMakeEqual(a: string, b: string, c: string)
  requires |a| == |b| == |c|
{
  forall i | 0 <= i < |a| ::
    HasSwap(a[i], b[i], c[i])
  // exists swapWithA: bool :: ValidSwapChoice(a[i], b[i], c[i], swapWithA)
}

// Characterize ValidSwapChoice without existential
ghost predicate HasValidSwapAtPos(a_i: char, b_i: char, c_i: char)
{
  c_i == a_i || c_i == b_i
}

// This is the key bridge lemma: connect HasValidSwapAtPos to ValidSwapChoice
lemma HasValidSwapImpliesExists(a_i: char, b_i: char, c_i: char)
  requires HasValidSwapAtPos(a_i, b_i, c_i)
  ensures exists sw: bool :: ValidSwapChoice(a_i, b_i, c_i, sw)
{
  if c_i == a_i {
    assert ValidSwapChoice(a_i, b_i, c_i, false);
  } else {
    assert ValidSwapChoice(a_i, b_i, c_i, true);
  }
}

lemma NotHasValidSwapImpliesNoExists(a_i: char, b_i: char, c_i: char)
  requires !HasValidSwapAtPos(a_i, b_i, c_i)
  ensures !(exists sw: bool :: ValidSwapChoice(a_i, b_i, c_i, sw))
{
  assert !ValidSwapChoice(a_i, b_i, c_i, true);
  assert !ValidSwapChoice(a_i, b_i, c_i, false);
}

// Bridge between concrete check and CanMakeEqual - proven by explicit quantifier manipulation
lemma AllHasValidSwapImpliesCanMakeEqual(a: string, b: string, c: string)
  requires |a| == |b| == |c|
  requires forall i | 0 <= i < |a| :: HasValidSwapAtPos(a[i], b[i], c[i])
  ensures CanMakeEqual(a, b, c)
{
  // Use a ghost function to pick witnesses, so Z3 can skolemize
  ghost var witnesses := seq(|a|, (k: int) requires 0 <= k < |a| => if c[k] == a[k] then false else true);
  assert |witnesses| == |a|;
  // Force the CanMakeEqual term into the context to trigger unfolding
  ghost var tmp := CanMakeEqual(a, b, c);
  forall i | 0 <= i < |a|
    ensures exists swapWithA: bool :: ValidSwapChoice(a[i], b[i], c[i], swapWithA)
  {
    if c[i] == a[i] {
      assert ValidSwapChoice(a[i], b[i], c[i], false);
    } else {
      assert HasValidSwapAtPos(a[i], b[i], c[i]);
      assert c[i] == b[i];
      assert ValidSwapChoice(a[i], b[i], c[i], true);
    }
  }
}

lemma SomeNotHasValidSwapImpliesNotCanMakeEqual(a: string, b: string, c: string, k: int)
  requires |a| == |b| == |c|
  requires 0 <= k < |a|
  requires !HasValidSwapAtPos(a[k], b[k], c[k])
  ensures !CanMakeEqual(a, b, c)
{
  NotHasValidSwapImpliesNoExists(a[k], b[k], c[k]);
}

method ThreeStrings(a: string, b: string, c: string) returns (result: bool)
  requires |a| == |b| == |c|
  ensures result == CanMakeEqual(a, b, c)
{
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j | 0 <= j < i :: HasValidSwapAtPos(a[j], b[j], c[j])
  {
    if a[i] != c[i] && b[i] != c[i] {
      assert !HasValidSwapAtPos(a[i], b[i], c[i]);
      SomeNotHasValidSwapImpliesNotCanMakeEqual(a, b, c, i);
      return false;
    }
    i := i + 1;
  }
  AllHasValidSwapImpliesCanMakeEqual(a, b, c);
  return true;
}

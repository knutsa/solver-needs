// Sum of a sequence of integers
ghost function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

// A valid dice face: the six-faced die has faces {2, 3, 4, 5, 6, 7}
ghost predicate ValidDiceFace(v: int)
{
  2 <= v <= 7
}

// Every element in the sequence is a valid dice face
ghost predicate AllValidFaces(dice: seq<int>)
{
  forall i | 0 <= i < |dice| :: ValidDiceFace(dice[i])
}

// Construct a concrete dice sequence achieving a target sum.
// Each die starts at minimum face value 2; the extra (target - 2*numRolls) is
// distributed greedily, adding up to 5 to each die (since max face is 7 = 2+5).
ghost function BuildDiceWitness(extra: int, numLeft: int): seq<int>
  requires numLeft >= 0
  decreases numLeft
{
  if numLeft == 0 then []
  else if numLeft == 1 then [2 + extra]
  else
    var add := if extra > 5 then 5 else if extra < 0 then 0 else extra;
    [2 + add] + BuildDiceWitness(extra - add, numLeft - 1)
}

// Build a witness dice sequence for the given target and number of rolls
ghost function DiceWitness(target: int, numRolls: int): seq<int>
  requires numRolls >= 1
{
  BuildDiceWitness(target - 2 * numRolls, numRolls)
}

// numRolls is a correct answer for target iff there exists a sequence of
// numRolls dice faces (each in {2..7}) whose sum equals target.
ghost predicate IsCorrectAnswer(target: int, numRolls: int)
{
  numRolls >= 1 &&
  exists dice: seq<int> :: |dice| == numRolls &&
    AllValidFaces(dice) &&
    SumSeq(dice) == target
}

// ========== Helper Lemmas ==========


lemma SumSeqPrepend(v: int, s: seq<int>)
  ensures SumSeq([v] + s) == v + SumSeq(s)
  decreases |s|
{
  var vs := [v] + s;
  if |s| == 0 {
    assert vs == [v];
    // Inlined from SumSeqSingleton(v)
    assert [(v)][..0] == [];
    assert SumSeq([v]) == v;
  } else {
    assert vs[..|vs|-1] == [v] + s[..|s|-1];
    assert vs[|vs|-1] == s[|s|-1];
    SumSeqPrepend(v, s[..|s|-1]);
  }
}

lemma BuildDiceWitnessLength(extra: int, numLeft: int)
  requires numLeft >= 0
  ensures |BuildDiceWitness(extra, numLeft)| == numLeft
  decreases numLeft
{
  if numLeft <= 1 {}
  else {
    var add := if extra > 5 then 5 else if extra < 0 then 0 else extra;
    BuildDiceWitnessLength(extra - add, numLeft - 1);
  }
}

lemma BuildDiceWitnessValid(extra: int, numLeft: int)
  requires numLeft >= 0
  requires 0 <= extra <= 5 * numLeft
  ensures AllValidFaces(BuildDiceWitness(extra, numLeft))
  decreases numLeft
{
  if numLeft == 0 {
  } else if numLeft == 1 {
  } else {
    var add := if extra > 5 then 5 else if extra < 0 then 0 else extra;
    assert 0 <= add <= 5;
    assert 0 <= extra - add <= 5 * (numLeft - 1);
    BuildDiceWitnessValid(extra - add, numLeft - 1);
    BuildDiceWitnessLength(extra - add, numLeft - 1);
    var rest := BuildDiceWitness(extra - add, numLeft - 1);
    assert AllValidFaces(rest);
    assert ValidDiceFace(2 + add);
    var bw := BuildDiceWitness(extra, numLeft);
    assert bw == [2 + add] + rest;
    forall j | 0 <= j < |bw|
      ensures ValidDiceFace(bw[j])
    {
      if j == 0 {
        assert bw[0] == 2 + add;
      } else {
        assert bw[j] == rest[j - 1];
      }
    }
  }
}

lemma BuildDiceWitnessSum(extra: int, numLeft: int)
  requires numLeft >= 0
  requires 0 <= extra <= 5 * numLeft
  ensures SumSeq(BuildDiceWitness(extra, numLeft)) == 2 * numLeft + extra
  decreases numLeft
{
  if numLeft == 0 {
  } else if numLeft == 1 {
    // Inlined from SumSeqSingleton(2 + extra)
    assert [(2 + extra)][..0] == [];
    assert SumSeq([(2 + extra)]) == (2 + extra);
  } else {
    var add := if extra > 5 then 5 else if extra < 0 then 0 else extra;
    assert 0 <= extra - add <= 5 * (numLeft - 1);
    BuildDiceWitnessSum(extra - add, numLeft - 1);
    var rest := BuildDiceWitness(extra - add, numLeft - 1);
    assert SumSeq(rest) == 2 * (numLeft - 1) + (extra - add);
    SumSeqPrepend(2 + add, rest);
    assert SumSeq([2 + add] + rest) == (2 + add) + SumSeq(rest);
    assert BuildDiceWitness(extra, numLeft) == [2 + add] + rest;
  }
}

lemma DiceRollingCorrectness(val: int, r: int)


// ========== Method ==========

method DiceRolling(x: seq<int>) returns (rolls: seq<int>)
  requires forall i | 0 <= i < |x| :: x[i] >= 2
  ensures |rolls| == |x|
  ensures forall i | 0 <= i < |rolls| :: IsCorrectAnswer(x[i], rolls[i])
{
  rolls := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |rolls| == i
    invariant forall j | 0 <= j < i :: IsCorrectAnswer(x[j], rolls[j])
  {
    var val := x[i];
    var r: int;
    if val <= 7 {
      r := 1;
      assert 2 <= val <= 7;
      // Inlined from DiceRollingCorrectness(val, 1)
      var extra := (val) - 2 * (1);
      assert 0 <= extra <= 5 * (1);
      BuildDiceWitnessLength(extra, (1));
      BuildDiceWitnessValid(extra, (1));
      BuildDiceWitnessSum(extra, (1));
      var dice := BuildDiceWitness(extra, (1));
      assert |dice| == (1);
      assert AllValidFaces(dice);
      assert SumSeq(dice) == (val);
      assert IsCorrectAnswer(val, 1);
    } else {
      r := val / 7;
      if val % 7 != 0 {
        r := r + 1;
      }
      assert val / 7 >= 1;
      assert r >= 1;
      // Case split to prove 2*r <= val <= 7*r
      if val % 7 == 0 {
        assert r == val / 7;
        assert val == 7 * r;
        assert 2 * r <= 7 * r;
      } else {
        assert r == val / 7 + 1;
        assert val == 7 * (val / 7) + val % 7;
        assert 7 * r == 7 * (val / 7) + 7;
        assert val % 7 >= 1;
        assert val % 7 < 7;
        assert val < 7 * r;
        assert val - 2 * r == 5 * (val / 7) + val % 7 - 2;
        assert 5 * (val / 7) >= 5;
        assert val - 2 * r >= 4;
      }
      assert 2 * r <= val <= 7 * r;
      // Inlined from DiceRollingCorrectness(val, r)
      var extra := (val) - 2 * (r);
      assert 0 <= extra <= 5 * (r);
      BuildDiceWitnessLength(extra, (r));
      BuildDiceWitnessValid(extra, (r));
      BuildDiceWitnessSum(extra, (r));
      var dice := BuildDiceWitness(extra, (r));
      assert |dice| == (r);
      assert AllValidFaces(dice);
      assert SumSeq(dice) == (val);
      assert IsCorrectAnswer(val, r);
    }
    rolls := rolls + [r];
    i := i + 1;
  }
}

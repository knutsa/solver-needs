ghost function Delta(c: char): int
{
  if c == '-' then -1 else 1
}

ghost function SumDeltas(s: seq<char>): int
  decreases |s|
{
  if |s| == 0 then 0
  else SumDeltas(s[..|s|-1]) + Delta(s[|s|-1])
}

// A valid execution: starting with `init` stones (>= 0), the pile
// never goes negative at any point during the sequence of operations.
ghost predicate ValidExecution(s: seq<char>, init: int)
{
  init >= 0 &&
  forall k | 0 <= k <= |s| :: init + SumDeltas(s[..k]) >= 0
}

ghost function FinalPileSize(s: seq<char>, init: int): int
{
  init + SumDeltas(s)
}


method PileOfStones(s: seq<char>) returns (result: int)
  // There exists a valid initial pile size that yields this result
  ensures exists init: nat :: ValidExecution(s, init) && FinalPileSize(s, init) == result
  // No valid initial pile size yields a smaller final pile
  ensures forall init: nat :: ValidExecution(s, init) ==> FinalPileSize(s, init) >= result
{
  result := 0;
  var i := 0;
  ghost var absorbed := 0;
  ghost var minK := 0;

  while i < |s|
    invariant 0 <= i <= |s|
    invariant result >= 0
    invariant absorbed >= 0
    invariant result == absorbed + SumDeltas(s[..i])
    invariant forall k | 0 <= k <= i :: absorbed + SumDeltas(s[..k]) >= 0
    invariant 0 <= minK <= i
    invariant SumDeltas(s[..minK]) == -absorbed
  {
    assert s[..i+1] == s[..i] + [s[i]];
    // Inlined from SumDeltasAppend(s[..i], s[i])
    var t := (s[..i]) + [(s[i])];
    assert t[..|t|-1] == (s[..i]);
    assert SumDeltas(s[..i] + [s[i]]) == SumDeltas(s[..i]) + Delta(s[i]);

    if s[i] == '-' {
      if result > 0 {
        result := result - 1;
      } else {
        absorbed := absorbed + 1;
        minK := i + 1;
      }
    } else {
      result := result + 1;
    }
    i := i + 1;
  }

  assert s[..|s|] == s;

  // Witness for first postcondition
  assert ValidExecution(s, absorbed);
  assert FinalPileSize(s, absorbed) == result;

  // Second postcondition: minimality
  assert 0 <= minK <= |s|;
  forall init: nat | ValidExecution(s, init)
    ensures FinalPileSize(s, init) >= result
  {
    assert init + SumDeltas(s[..minK]) >= 0;
    assert init >= absorbed;
  }
}

ghost predicate InSeq(x: int, s: seq<int>)
{
  exists i | 0 <= i < |s| :: s[i] == x
}

// A line is possible iff it stops at every observed stop
ghost predicate PossibleLine(line: int, stops: seq<seq<int>>)
{
  forall k | 0 <= k < |stops| :: InSeq(line, stops[k])
}

lemma InSeqExtend(x: int, s: seq<int>, y: int)
  requires InSeq(x, s)
  ensures InSeq(x, s + [y])
{
  var w :| 0 <= w < |s| && s[w] == x;
  assert (s + [y])[w] == x;
}

method DetermineLine(stops: seq<seq<int>>) returns (result: seq<int>)
  // Soundness: every element in result is a possible line
  ensures forall i | 0 <= i < |result| :: PossibleLine(result[i], stops)
  // Completeness: every possible line appears in result
  ensures forall k | 0 <= k < |stops| :: forall j | 0 <= j < |stops[k]| ::
                                           PossibleLine(stops[k][j], stops) ==> InSeq(stops[k][j], result)
{
  if |stops| == 0 { result := []; return; }
  result := stops[0];
  for k := 1 to |stops|
    invariant forall i | 0 <= i < |result| :: forall m | 0 <= m < k :: InSeq(result[i], stops[m])
    invariant forall x :: (forall m | 0 <= m < k :: InSeq(x, stops[m])) ==> InSeq(x, result)
  {
    var newResult: seq<int> := [];
    for i := 0 to |result|
      invariant forall idx | 0 <= idx < |newResult| :: InSeq(newResult[idx], stops[k]) && InSeq(newResult[idx], result)
      invariant forall idx | 0 <= idx < i :: InSeq(result[idx], stops[k]) ==> InSeq(result[idx], newResult)
    {
      var found := false;
      for j := 0 to |stops[k]|
        invariant found <==> exists j' | 0 <= j' < j :: result[i] == stops[k][j']
      {
        if result[i] == stops[k][j] {
          found := true;
        }
      }
      if found {
        ghost var oldNR := newResult;
        newResult := newResult + [result[i]];
        // Prove invariant 2 is maintained for all idx < i+1
        forall idx | 0 <= idx < i + 1
          ensures InSeq(result[idx], stops[k]) ==> InSeq(result[idx], newResult)
        {
          if idx < i {
            if InSeq(result[idx], stops[k]) {
              assert InSeq(result[idx], oldNR);
              var w :| 0 <= w < |oldNR| && oldNR[w] == result[idx];
              assert newResult[w] == result[idx];
            }
          } else {
            // idx == i, result[i] is last element of newResult
            if InSeq(result[i], stops[k]) {
              assert newResult[|oldNR|] == result[i];
            }
          }
        }
        // Prove invariant 1 is maintained for old elements
        forall idx | 0 <= idx < |oldNR|
          ensures InSeq(newResult[idx], stops[k]) && InSeq(newResult[idx], result)
        {
          assert newResult[idx] == oldNR[idx];
        }
      }
    }

    // Prove soundness for next iteration
    assert forall i | 0 <= i < |newResult| :: forall m | 0 <= m < k + 1 :: InSeq(newResult[i], stops[m])
    by {
      forall i | 0 <= i < |newResult|
        ensures forall m | 0 <= m < k + 1 :: InSeq(newResult[i], stops[m])
      {
        assert InSeq(newResult[i], stops[k]);
        assert InSeq(newResult[i], result);
        var ridx :| 0 <= ridx < |result| && result[ridx] == newResult[i];
        forall m | 0 <= m < k
          ensures InSeq(newResult[i], stops[m])
        {
          assert InSeq(result[ridx], stops[m]);
        }
      }
    }

    // Prove completeness for next iteration
    assert forall x :: (forall m | 0 <= m < k + 1 :: InSeq(x, stops[m])) ==> InSeq(x, newResult)
    by {
      forall x | (forall m | 0 <= m < k + 1 :: InSeq(x, stops[m]))
        ensures InSeq(x, newResult)
      {
        assert forall m | 0 <= m < k :: InSeq(x, stops[m]);
        assert InSeq(x, result);
        var ridx :| 0 <= ridx < |result| && result[ridx] == x;
        assert InSeq(x, stops[k]);
        assert InSeq(result[ridx], stops[k]);
        assert InSeq(result[ridx], newResult);
      }
    }

    result := newResult;
  }
}

method SameElements(a: seq<int>, b: seq<int>) returns (same: bool)
{
  if |a| != |b| { return false; }
  for i := 0 to |a| {
    var found := false;
    for j := 0 to |b| {
      if a[i] == b[j] { found := true; }
    }
    if !found { return false; }
  }
  for i := 0 to |b| {
    var found := false;
    for j := 0 to |a| {
      if b[i] == a[j] { found := true; }
    }
    if !found { return false; }
  }
  return true;
}

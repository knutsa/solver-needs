ghost predicate PointInSegment(p: int, seg: (int, int))
{
  seg.0 <= p <= seg.1
}

ghost predicate PointCoveredByAny(p: int, segments: seq<(int, int)>)
{
  exists i | 0 <= i < |segments| :: PointInSegment(p, segments[i])
}

ghost predicate StrictlyIncreasing(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] < s[j]
}


method PointsInSegments(segments: seq<(int, int)>, m: int) returns (result: seq<int>)
  requires m >= 0
  requires forall i | 0 <= i < |segments| :: 1 <= segments[i].0 <= segments[i].1 <= m
  // Every output point is a valid point in [1, m] that is not covered by any segment
  ensures forall i | 0 <= i < |result| :: 1 <= result[i] <= m
  ensures forall i | 0 <= i < |result| :: !PointCoveredByAny(result[i], segments)
  // Every uncovered point in [1, m] appears in the result (completeness)
  ensures forall p | 1 <= p <= m :: !PointCoveredByAny(p, segments) ==>
    (exists j | 0 <= j < |result| :: result[j] == p)
  // Output is in strictly increasing order (implies no duplicates)
  ensures StrictlyIncreasing(result)
{
  var A := seq(m, (_: int) => true);
  var i := 0;
  while i < |segments|
    invariant 0 <= i <= |segments|
    invariant |A| == m
    invariant forall p :: 0 <= p < m ==>
      (A[p] <==> forall idx :: 0 <= idx < i ==> !PointInSegment(p + 1, segments[idx]))
  {
    var a := segments[i].0;
    var b := segments[i].1;
    ghost var A_before := A;
    var j := a - 1;
    while j < b
      invariant a - 1 <= j <= b
      invariant |A| == m
      invariant forall p :: 0 <= p < m ==>
        if a - 1 <= p < j then A[p] == false
        else A[p] == A_before[p]
    {
      if 0 <= j < |A| {
        A := A[j := false];
      }
      j := j + 1;
    }

    forall p | 0 <= p < m
      ensures A[p] <==> forall idx :: 0 <= idx < i + 1 ==> !PointInSegment(p + 1, segments[idx])
    {
      if a - 1 <= p < b {
        assert PointInSegment(p + 1, segments[i]);
      } else {
        assert !PointInSegment(p + 1, segments[i]);
        assert A[p] == A_before[p];
      }
    }

    i := i + 1;
  }

  forall p | 0 <= p < m
    ensures A[p] <==> !PointCoveredByAny(p + 1, segments)
  {
  }

  result := [];
  var k := 0;
  while k < m
    invariant 0 <= k <= m
    invariant |A| == m
    invariant forall p :: 0 <= p < m ==> (A[p] <==> !PointCoveredByAny(p + 1, segments))
    invariant forall q | 0 <= q < |result| :: 1 <= result[q] <= m
    invariant forall q | 0 <= q < |result| :: !PointCoveredByAny(result[q], segments)
    invariant forall p | 1 <= p <= k :: !PointCoveredByAny(p, segments) ==>
      exists q | 0 <= q < |result| :: result[q] == p
    invariant StrictlyIncreasing(result)
    invariant |result| > 0 ==> result[|result| - 1] <= k
  {
    ghost var old_result := result;
    if A[k] {
      // Inlined from StrictlyIncreasingAppend(result, k + 1)
      assert StrictlyIncreasing(result + [(k + 1)]);
      result := result + [k + 1];
    }
    assert forall q | 0 <= q < |old_result| :: result[q] == old_result[q];
    k := k + 1;
  }
}

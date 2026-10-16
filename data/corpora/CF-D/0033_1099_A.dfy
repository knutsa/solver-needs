// Clamp negative weights to zero, per the problem rules
ghost function Max0(x: int): int {
  if x < 0 then 0 else x
}

// "Each second the following sequence of events happens" at a given height:
//  1. Snowball's weight increases by current height
//  2. If stone 1 is at this height, snowball loses u1 weight (clamped to 0)
//  3. If stone 2 is at this height, snowball loses u2 weight (clamped to 0)
ghost function WeightAfterHeight(weight: int, height: int,
                           u1: int, d1: int, u2: int, d2: int): int
{
  var afterGain  := weight + height;
  var afterStone1 := if height == d1 then Max0(afterGain - u1) else afterGain;
  var afterStone2 := if height == d2 then Max0(afterStone1 - u2) else afterStone1;
  afterStone2
}

// The descending sequence of heights the snowball visits: [h, h-1, ..., 1, 0]
ghost function Heights(h: int): seq<int>
  decreases if h >= 0 then h + 1 else 0
{
  if h < 0 then []
  else [h] + Heights(h - 1)
}

// The snowball's weight after rolling through the given sequence of heights
ghost function RollThrough(w: int, heights: seq<int>,
                     u1: int, d1: int, u2: int, d2: int): int
  decreases |heights|
{
  if |heights| == 0 then w
  else RollThrough(WeightAfterHeight(w, heights[0], u1, d1, u2, d2),
                   heights[1..], u1, d1, u2, d2)
}

method Snowball(w: int, h: int, u1: int, d1: int, u2: int, d2: int) returns (finalWeight: int)
  ensures finalWeight == RollThrough(w, Heights(h), u1, d1, u2, d2)
{
  finalWeight := w;
  var i := h;
  while i >= 0
    invariant i >= -1 || i == h
    invariant RollThrough(w, Heights(h), u1, d1, u2, d2) == RollThrough(finalWeight, Heights(i), u1, d1, u2, d2)
    decreases i + 1
  {
    var oldWeight := finalWeight;
    finalWeight := finalWeight + i;
    if i == d1 {
      finalWeight := finalWeight - u1;
      if finalWeight < 0 {
        finalWeight := 0;
      }
    }
    if i == d2 {
      finalWeight := finalWeight - u2;
      if finalWeight < 0 {
        finalWeight := 0;
      }
    }
    assert finalWeight == WeightAfterHeight(oldWeight, i, u1, d1, u2, d2);
    assert Heights(i) == [i] + Heights(i - 1);
    i := i - 1;
  }
}

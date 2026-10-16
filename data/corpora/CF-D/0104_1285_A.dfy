ghost function CountChar(s: string, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

// A position p is reachable if we can choose how many L-commands to execute
// (0..total_L) and how many R-commands to execute (0..total_R) such that
// the net displacement nr - nl equals p. This models the problem: each
// command is independently either executed (keeping its effect) or ignored.
ghost predicate Reachable(s: string, p: int)
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  exists nl: int, nr: int | 0 <= nl <= l && 0 <= nr <= r :: p == nr - nl
}

ghost function ReachablePositions(s: string): set<int>
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  set p: int | -l <= p <= r && Reachable(s, p)
}

lemma CountCharNonNeg(s: string, c: char)
  ensures CountChar(s, c) >= 0
  decreases |s|
{
  if |s| > 0 {
    CountCharNonNeg(s[..|s|-1], c);
  }
}

lemma CountCharStep(s: string, c: char, i: int)
  requires 0 <= i < |s|
  ensures CountChar(s[..i+1], c) == CountChar(s[..i], c) + (if s[i] == c then 1 else 0)
{
  assert s[..i+1][..i] == s[..i];
}

lemma ReachableShiftDown(s: string, p: int)
  requires Reachable(s, p)
  requires p > -CountChar(s, 'L')
  ensures Reachable(s, p - 1)
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  var nl: int, nr: int :| 0 <= nl <= l && 0 <= nr <= r && p == nr - nl;
  if nl < l {
    assert 0 <= nl + 1 <= l;
    assert 0 <= nr <= r;
    assert p - 1 == nr - (nl + 1);
  } else {
    assert nr > 0;
    assert 0 <= nl <= l;
    assert 0 <= nr - 1 <= r;
    assert p - 1 == (nr - 1) - nl;
  }
}

lemma AllReachable(s: string, p: int)
  requires -CountChar(s, 'L') <= p <= CountChar(s, 'R')
  ensures Reachable(s, p)
  decreases if p < 0 then -p else 0
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  CountCharNonNeg(s, 'L');
  CountCharNonNeg(s, 'R');
  if p >= 0 {
    assert 0 <= 0 <= l;
    assert 0 <= p <= r;
    assert p == p - 0;
  } else {
    AllReachable(s, p + 1);
    ReachableShiftDown(s, p + 1);
  }
}

lemma IntRangeSize(lo: int, hi: int)
  requires lo <= hi + 1
  ensures |(set p: int | lo <= p <= hi)| == if lo <= hi then hi - lo + 1 else 0
  decreases hi - lo + 1
{
  if lo > hi {
    assert (set p: int | lo <= p <= hi) == {};
  } else if lo == hi {
    assert (set p: int | lo <= p <= hi) == {lo};
  } else {
    var s1 := set p: int | lo <= p <= hi;
    var s2 := set p: int | lo <= p <= hi - 1;
    assert hi in s1;
    assert hi !in s2;
    assert s1 == s2 + {hi} by {
      forall p | p in s1
        ensures p in s2 || p == hi
      {}
      forall p | p in s2
        ensures p in s1
      {}
    }
    IntRangeSize(lo, hi - 1);
  }
}

lemma ReachableSetEqualsRange(s: string)
  ensures ReachablePositions(s) == (set p: int | -CountChar(s, 'L') <= p <= CountChar(s, 'R'))
{
  var l := CountChar(s, 'L');
  var r := CountChar(s, 'R');
  CountCharNonNeg(s, 'L');
  CountCharNonNeg(s, 'R');
  var rp := ReachablePositions(s);
  var full := set p: int | -l <= p <= r;

  forall p | p in full
    ensures p in rp
  {
    AllReachable(s, p);
  }
}

method MezoPlayingZoma(s: string) returns (positions: int)
  requires forall i | 0 <= i < |s| :: s[i] == 'L' || s[i] == 'R'
  ensures positions == |ReachablePositions(s)|
{
  var l := 0;
  var r := 0;
  for i := 0 to |s|
    invariant l == CountChar(s[..i], 'L')
    invariant r == CountChar(s[..i], 'R')
  {
    CountCharStep(s, 'L', i);
    CountCharStep(s, 'R', i);
    if s[i] == 'L' {
      l := l + 1;
    } else if s[i] == 'R' {
      r := r + 1;
    }
  }
  assert s[..|s|] == s;

  CountCharNonNeg(s, 'L');
  CountCharNonNeg(s, 'R');
  ReachableSetEqualsRange(s);
  IntRangeSize(-l, r);

  positions := l + r + 1;
}

ghost function Sum(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else Sum(s[..|s|-1]) + s[|s|-1]
}

// Occupancy after processing all stops described by a and b:
// total who boarded minus total who exited
ghost function Occupancy(a: seq<int>, b: seq<int>): int
  requires |a| == |b|
{
  Sum(b) - Sum(a)
}

// A capacity is valid if it is non-negative and never exceeded
// at any stop (after the first k stops, for every k from 1 to n)
ghost predicate IsValidCapacity(c: int, n: int, a: seq<int>, b: seq<int>)
  requires 0 <= n <= |a| && n <= |b|
{
  c >= 0 &&
  forall k | 1 <= k <= n :: Occupancy(a[..k], b[..k]) <= c
}

// The minimum capacity: valid, and no smaller value is valid
ghost predicate IsMinimumCapacity(c: int, n: int, a: seq<int>, b: seq<int>)
  requires 0 <= n <= |a| && n <= |b|
{
  IsValidCapacity(c, n, a, b) &&
  forall c' | 0 <= c' < c :: !IsValidCapacity(c', n, a, b)
}

lemma SumAppend(s: seq<int>, x: int)
  ensures Sum(s + [x]) == Sum(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    assert (s + [x])[..|s + [x]| - 1] == s;
  }
}

method Tram(n: int, a: seq<int>, b: seq<int>) returns (capacity: int)
  requires 0 <= n <= |a| && n <= |b|
  ensures IsMinimumCapacity(capacity, n, a, b)
{
  var current := 0;
  capacity := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant current == Occupancy(a[..i], b[..i])
    invariant capacity >= 0
    invariant forall k | 1 <= k <= i :: Occupancy(a[..k], b[..k]) <= capacity
    invariant capacity == 0 || exists k | 1 <= k <= i :: capacity == Occupancy(a[..k], b[..k])
  {
    assert a[..i+1] == a[..i] + [a[i]];
    assert b[..i+1] == b[..i] + [b[i]];
    SumAppend(a[..i], a[i]);
    SumAppend(b[..i], b[i]);
    current := current - a[i] + b[i];
    if current > capacity {
      capacity := current;
    }
    i := i + 1;
  }
}

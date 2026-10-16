// The position in a cyclic sequence of given period for a given year.
// Year 1 starts at position 0; each subsequent year advances by 1, wrapping around.
ghost function CyclicIndex(year: int, period: int): int
  requires year >= 1
  requires period > 0
  ensures 0 <= CyclicIndex(year, period) < period
{
  (year - 1) % period
}

// The Gapja name for a year: concatenation of the cyclically selected
// string from each of the two naming sequences.
ghost function GapjaName(year: int, s: seq<string>, t: seq<string>): string
  requires year >= 1
  requires |s| > 0
  requires |t| > 0
{
  s[CyclicIndex(year, |s|)] + t[CyclicIndex(year, |t|)]
}

method NewYearNaming(n: int, m: int, s: seq<string>, t: seq<string>, queries: seq<int>) returns (results: seq<string>)
  requires n > 0 && m > 0
  requires |s| == n && |t| == m
  requires forall i | 0 <= i < |queries| :: queries[i] >= 1
  ensures |results| == |queries|
  ensures forall i | 0 <= i < |queries| :: results[i] == GapjaName(queries[i], s, t)
{
  results := [];
  for i := 0 to |queries|
    invariant |results| == i
    invariant forall j | 0 <= j < i :: results[j] == GapjaName(queries[j], s, t)
  {
    var x := queries[i] - 1;
    assert queries[i] >= 1;
    assert x == queries[i] - 1;
    assert x % n == CyclicIndex(queries[i], n);
    assert x % m == CyclicIndex(queries[i], m);
    results := results + [s[x % n] + t[x % m]];
  }
}

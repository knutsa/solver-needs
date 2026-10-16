// --- Specification: Vus the Cossack and a Contest ---

// Sum of all elements in a sequence
ghost function SumSeq(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else SumSeq(s[..|s|-1]) + s[|s|-1]
}

// Every person receives at least one item
ghost predicate AllAtLeastOne(s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] >= 1
}

// A valid distribution of `supply` items among `n` people, each getting at least 1
ghost predicate ValidDistribution(dist: seq<int>, n: int, supply: int)
{
  n >= 0 &&
  |dist| == n &&
  AllAtLeastOne(dist) &&
  SumSeq(dist) <= supply
}

// A valid rewarding: valid distributions of both pens and notebooks
ghost predicate ValidRewarding(penDist: seq<int>, noteDist: seq<int>, n: int, m: int, k: int)
{
  ValidDistribution(penDist, n, m) && ValidDistribution(noteDist, n, k)
}

// The minimal-cost distribution: give exactly 1 item to each person
ghost function UniformDist(n: nat): (r: seq<int>)
  ensures |r| == n
  ensures forall i | 0 <= i < n :: r[i] == 1
  ensures SumSeq(r) == n
  decreases n
{
  if n == 0 then [] else UniformDist(n - 1) + [1]
}

// Mathematical fact: any distribution giving everyone >= 1 item uses >= n items total.
// This proves UniformDist is optimal, so if it fails, no distribution can succeed.
ghost function SumLowerBound(s: seq<int>): (b: bool)
  ensures AllAtLeastOne(s) ==> SumSeq(s) >= |s|
  decreases |s|
{
  if |s| == 0 then true
  else var _ := SumLowerBound(s[..|s|-1]); true
}

method VusContest(n: int, m: int, k: int) returns (result: string)
  requires n >= 1
  ensures result == "Yes" || result == "No"
  ensures result == "Yes" <==> ValidRewarding(UniformDist(n), UniformDist(n), n, m, k)
{
  if k < n || m < n {
    result := "No";
  } else {
    result := "Yes";
  }
}

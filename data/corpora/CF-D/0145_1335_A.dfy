ghost predicate ValidDistribution(n: int, a: int, b: int) {
  a > 0 && b > 0 && a > b && a + b == n
}

ghost function CountDistributions(n: int, hi: int): int
  requires hi >= 0
  decreases hi
{
  if hi < 1 then 0
  else CountDistributions(n, hi - 1) + (if ValidDistribution(n, n - hi, hi) then 1 else 0)
}

lemma CountDistributionsLemma(n: int, hi: int)
  requires hi >= 0
  requires n >= 1
  ensures hi <= (n - 1) / 2 ==> CountDistributions(n, hi) == hi
  ensures hi > (n - 1) / 2 ==> CountDistributions(n, hi) == (n - 1) / 2
  decreases hi
{
  if hi < 1 {
  } else {
    CountDistributionsLemma(n, hi - 1);
    if 2 * hi < n {
      assert ValidDistribution(n, n - hi, hi);
    } else {
      assert !ValidDistribution(n, n - hi, hi);
    }
  }
}

method Candies(n: int) returns (ways: int)
  requires n >= 1
  ensures ways == CountDistributions(n, n - 1)
{
  CountDistributionsLemma(n, n - 1);
  if n <= 2 {
    ways := 0;
  } else {
    ways := (n - 1) / 2;
  }
}

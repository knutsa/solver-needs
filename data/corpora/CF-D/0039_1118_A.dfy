// --- Formal Specification ---

// A valid purchase of exactly n liters using 1-liter and 2-liter bottles
ghost predicate IsValidPurchase(ones: int, twos: int, n: int)
{
  ones >= 0 && twos >= 0 && ones + 2 * twos == n
}

// Total cost of purchasing ones 1-liter bottles at price a, twos 2-liter bottles at price b
ghost function PurchaseCost(ones: int, twos: int, a: int, b: int): int
{
  ones * a + twos * b
}

// The minimum cost to buy exactly n liters at prices a (per 1L) and b (per 2L).
// Any valid purchase is parameterized by twos in {0, ..., n/2} with ones = n - 2*twos.
// The total cost n*a + twos*(b - 2*a) is linear in twos, so the minimum
// over the integer interval [0, n/2] is at one of the two endpoints.
ghost function MinCost(n: int, a: int, b: int): int
  requires n >= 0
{
  var allOnesCost := PurchaseCost(n, 0, a, b);
  var maxTwosCost := PurchaseCost(n % 2, n / 2, a, b);
  if allOnesCost <= maxTwosCost then allOnesCost else maxTwosCost
}

// --- Implementation ---

method WaterBuying(queries: seq<(int, int, int)>) returns (results: seq<int>)
  requires forall i | 0 <= i < |queries| :: queries[i].0 >= 0
  ensures |results| == |queries|
  ensures forall i | 0 <= i < |queries| ::
    results[i] == MinCost(queries[i].0, queries[i].1, queries[i].2)
{
  results := [];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant |results| == i
    invariant forall j | 0 <= j < i ::
      results[j] == MinCost(queries[j].0, queries[j].1, queries[j].2)
  {
    var (n, a, b) := queries[i];
    var two := 2 * a;
    var m := if two < b then two else b;
    var ans := (n / 2) * m + (n % 2) * a;

    // Key identity for n >= 0
    assert (n / 2) * 2 + (n % 2) == n;

    var allOnesCost := PurchaseCost(n, 0, a, b);
    var maxTwosCost := PurchaseCost(n % 2, n / 2, a, b);

    assert allOnesCost == n * a;
    assert maxTwosCost == (n % 2) * a + (n / 2) * b;

    if two < b {
      // 2*a < b: all 1-liter bottles is cheaper
      assert ans == (n / 2) * (2 * a) + (n % 2) * a;
      // Factor out a: ans = ((n/2)*2 + n%2) * a = n * a
      assert (n / 2) * (2 * a) == ((n / 2) * 2) * a;
      assert ans == ((n / 2) * 2) * a + (n % 2) * a;
      assert ans == ((n / 2) * 2 + (n % 2)) * a;
      assert ans == n * a;

      // Show allOnesCost <= maxTwosCost: difference = (n/2)*(2*a - b) <= 0
      assert n / 2 >= 0;
      assert 2 * a - b < 0;
      assert (n / 2) * (2 * a - b) <= 0;
      assert n * a - ((n % 2) * a + (n / 2) * b) == (n / 2) * (2 * a - b);
      assert allOnesCost <= maxTwosCost;
    } else {
      // 2*a >= b: max 2-liter bottles is cheaper
      assert ans == (n / 2) * b + (n % 2) * a;
      assert ans == maxTwosCost;

      // Show maxTwosCost <= allOnesCost: difference = (n/2)*(2*a - b) >= 0
      assert n / 2 >= 0;
      assert 2 * a - b >= 0;
      assert (n / 2) * (2 * a - b) >= 0;
      assert n * a - ((n % 2) * a + (n / 2) * b) == (n / 2) * (2 * a - b);
      assert allOnesCost >= maxTwosCost;
    }

    assert ans == MinCost(n, a, b);

    results := results + [ans];
    i := i + 1;
  }
}

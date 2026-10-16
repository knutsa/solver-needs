// ── Formal Specification for the Coins Problem ──

// Sum of a sequence of integers.
ghost function Sum(a: seq<int>): int
  decreases |a|
{
  if |a| == 0 then 0 else Sum(a[..|a|-1]) + a[|a|-1]
}

// Every coin has a denomination in {1, ..., n}.
ghost predicate AllValid(coins: seq<int>, n: int)
{
  forall i | 0 <= i < |coins| :: 1 <= coins[i] <= n
}

// A valid coin selection: non-empty, all denominations in {1..n}, summing to S.
ghost predicate IsValidSelection(coins: seq<int>, n: int, S: int)
{
  |coins| >= 1 && AllValid(coins, n) && Sum(coins) == S
}

// Exactly k coins from {1, ..., n} can achieve sum S iff S lies in [k, k*n].
// Each coin contributes at least 1 (minimum denomination) and at most n
// (maximum denomination), so k coins yield a sum in [k, k*n].
// Every integer in that range is achievable.
ghost predicate Achievable(k: int, n: int, S: int)
{
  k >= 1 && n >= 1 && k <= S && S <= k * n
}

// Constructive witness for Achievable: use (k-1) coins of denomination n,
// plus one coin carrying the remainder S - (k-1)*n, which lies in [1, n]
// whenever Achievable(k, n, S) holds.
ghost function Witness(k: int, n: int, S: int): seq<int>
{
  if k >= 1 && n >= 1 && k <= S && S <= k * n then
    seq(k, i requires 0 <= i < k => if i < k - 1 then n else S - (k - 1) * n)
  else
    []
}

// Helper lemma: product of two non-negative integers is non-negative.
// This is the assertion Z3 struggles with under different random seeds.
lemma MulNonNeg(a: int, b: int)
  requires a >= 0
  requires b >= 0
  ensures a * b >= 0
{
  // Prove by induction on a
  if a == 0 {
    assert a * b == 0;
  } else {
    MulNonNeg(a - 1, b);
    assert (a - 1) * b >= 0;
    assert a * b == (a - 1) * b + b;
  }
}

// ── Method with contracts ──

method Coins(n: int, S: int) returns (minCoins: int)
  requires n >= 1
  requires S >= 1
  // Existence: minCoins coins from {1, ..., n} can achieve sum S
  ensures Achievable(minCoins, n, S)
  // Minimality: no fewer coins can achieve sum S
  ensures forall k | 1 <= k < minCoins :: !Achievable(k, n, S)
{
  minCoins := (S - 1) / n + 1;
  var q := (S - 1) / n;
  var r := (S - 1) % n;
  // Properties of integer division: S - 1 == q * n + r, 0 <= r < n
  assert S - 1 == q * n + r;
  assert 0 <= r < n;
  assert minCoins == q + 1;

  // Prove Achievable(minCoins, n, S):
  // 1. minCoins >= 1
  assert minCoins >= 1;
  // 2. minCoins <= S: since q*(n-1) >= 0 and r >= 0
  assert q >= 0;
  assert n - 1 >= 0;
  MulNonNeg(q, n - 1);
  assert q * (n - 1) >= 0;
  assert minCoins <= S;
  // 3. S <= minCoins * n: since r + 1 <= n
  assert r + 1 <= n;
  assert S <= minCoins * n;

  // Prove minimality: for k < minCoins, k*n < S so !Achievable
  forall k | 1 <= k < minCoins
    ensures !Achievable(k, n, S)
  {
    assert k <= q;
    assert k * n <= q * n;
    assert q * n <= S - 1;
    assert S > k * n;
  }
}

// ── Tests ──

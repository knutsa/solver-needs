ghost function Outcome(r: int, buyPrice: int, sellPrice: int, shares: int): int
{
  r - shares * buyPrice + shares * sellPrice
}

ghost predicate ValidTrade(r: int, buyPrice: int, shares: int)
{
  buyPrice > 0 && shares >= 0 && shares * buyPrice <= r
}

ghost predicate IsAchievable(result: int, r: int, s: seq<int>, b: seq<int>)
{
  result == r
  ||
  (exists i | 0 <= i < |s| :: exists j | 0 <= j < |b| :: exists k: nat ::
    ValidTrade(r, s[i], k) && result == Outcome(r, s[i], b[j], k))
}

ghost predicate IsOptimal(result: int, r: int, s: seq<int>, b: seq<int>)
{
  result >= r
  &&
  (forall i | 0 <= i < |s| :: forall j | 0 <= j < |b| :: forall k: nat ::
    ValidTrade(r, s[i], k) ==> Outcome(r, s[i], b[j], k) <= result)
}

lemma DivBound(k: nat, a: int, r: int)
  requires a > 0
  requires k * a <= r
  ensures k <= r / a
{
  if k > r / a {
    assert k >= r / a + 1;
    assert (r / a + 1) * a == (r / a) * a + a;
    assert r == (r / a) * a + r % a;
    assert 0 <= r % a < a;
  }
}

lemma MulMonoLeft(c: int, a: int, b: int)
  requires c >= 0
  requires a <= b
  ensures c * a <= c * b
{
}

lemma MulMonoRight(a: int, b: int, c: int)
  requires a <= b
  requires c >= 0
  ensures a * c <= b * c
{
}

method StockArbitraging(n: int, m: int, r: int, s: seq<int>, b: seq<int>) returns (maxBourles: int)
  requires |s| == n && n >= 1
  requires |b| == m && m >= 1
  requires r >= 1
  requires forall i | 0 <= i < n :: s[i] >= 1
  requires forall j | 0 <= j < m :: b[j] >= 1
  ensures IsAchievable(maxBourles, r, s, b)
  ensures IsOptimal(maxBourles, r, s, b)
{
  var minS := s[0];
  ghost var minIdx := 0;
  var i := 1;
  while i < |s|
    invariant 1 <= i <= |s|
    invariant 0 <= minIdx < i
    invariant minS == s[minIdx]
    invariant forall k | 0 <= k < i :: minS <= s[k]
  {
    if s[i] < minS {
      minS := s[i];
      minIdx := i;
    }
    i := i + 1;
  }

  var maxB := b[0];
  ghost var maxIdx := 0;
  i := 1;
  while i < |b|
    invariant 1 <= i <= |b|
    invariant 0 <= maxIdx < i
    invariant maxB == b[maxIdx]
    invariant forall k | 0 <= k < i :: maxB >= b[k]
  {
    if b[i] > maxB {
      maxB := b[i];
      maxIdx := i;
    }
    i := i + 1;
  }

  ghost var shares: nat := r / minS;
  var profit := r % minS + (r / minS) * maxB;

  if profit > r {
    maxBourles := profit;

    // === Prove IsAchievable ===
    assert shares * minS <= r by {
      assert r == shares * minS + r % minS;
      assert r % minS >= 0;
    }
    assert ValidTrade(r, s[minIdx], shares);
    assert r - shares * minS == r % minS by {
      assert r == shares * minS + r % minS;
    }
    assert Outcome(r, s[minIdx], b[maxIdx], shares) == maxBourles;

    // === Prove IsOptimal ===
    forall ii | 0 <= ii < |s|
      ensures forall jj | 0 <= jj < |b| :: forall kk: nat ::
        ValidTrade(r, s[ii], kk) ==> Outcome(r, s[ii], b[jj], kk) <= maxBourles
    {
      forall jj | 0 <= jj < |b|
        ensures forall kk: nat ::
          ValidTrade(r, s[ii], kk) ==> Outcome(r, s[ii], b[jj], kk) <= maxBourles
      {
        forall kk: nat | ValidTrade(r, s[ii], kk)
          ensures Outcome(r, s[ii], b[jj], kk) <= maxBourles
        {
          MulMonoLeft(kk, minS, s[ii]);
          assert kk * minS <= kk * s[ii];
          assert kk * minS <= r;
          DivBound(kk, minS, r);
          assert kk <= shares;

          if b[jj] <= s[ii] {
            MulMonoLeft(kk, b[jj], s[ii]);
            assert kk * b[jj] <= kk * s[ii];
          } else {
            assert b[jj] - s[ii] >= 1;
            assert maxB - minS >= b[jj] - s[ii];
            MulMonoRight(kk, shares, b[jj] - s[ii]);
            assert kk * (b[jj] - s[ii]) <= shares * (b[jj] - s[ii]);
            MulMonoLeft(shares, b[jj] - s[ii], maxB - minS);
            assert shares * (b[jj] - s[ii]) <= shares * (maxB - minS);
            assert kk * (b[jj] - s[ii]) <= shares * (maxB - minS);
            assert r - shares * minS == r % minS by {
              assert r == shares * minS + r % minS;
            }
            assert shares * (maxB - minS) == shares * maxB - shares * minS;
            assert r + shares * (maxB - minS) == r - shares * minS + shares * maxB;
            assert r - shares * minS + shares * maxB == r % minS + shares * maxB;
            assert r % minS + shares * maxB == maxBourles;
          }
        }
      }
    }
  } else {
    maxBourles := r;

    // === Prove IsOptimal ===
    forall ii | 0 <= ii < |s|
      ensures forall jj | 0 <= jj < |b| :: forall kk: nat ::
        ValidTrade(r, s[ii], kk) ==> Outcome(r, s[ii], b[jj], kk) <= r
    {
      forall jj | 0 <= jj < |b|
        ensures forall kk: nat ::
          ValidTrade(r, s[ii], kk) ==> Outcome(r, s[ii], b[jj], kk) <= r
      {
        forall kk: nat | ValidTrade(r, s[ii], kk)
          ensures Outcome(r, s[ii], b[jj], kk) <= r
        {
          if shares == 0 {
            assert r < minS by {
              assert r == shares * minS + r % minS;
              assert r == r % minS;
              assert r % minS < minS;
            }
            if kk >= 1 {
              MulMonoRight(1, kk, s[ii]);
              assert 1 * s[ii] <= kk * s[ii];
              assert s[ii] >= minS > r;
              assert kk * s[ii] > r;
              assert false;
            }
            assert kk == 0;
          } else {
            assert shares >= 1;
            assert profit <= r;
            assert shares * (maxB - minS) <= 0 by {
              assert profit == r % minS + shares * maxB;
              assert r == shares * minS + r % minS;
              assert profit - r == shares * maxB - shares * minS;
              assert shares * maxB - shares * minS == shares * (maxB - minS);
              assert profit - r <= 0;
            }
            if maxB > minS {
              assert maxB - minS >= 1;
              MulMonoRight(1, shares, maxB - minS);
              assert 1 * (maxB - minS) <= shares * (maxB - minS);
              assert 1 * (maxB - minS) == maxB - minS >= 1;
              assert shares * (maxB - minS) >= 1;
              assert false;
            }
            assert maxB <= minS;
            assert b[jj] <= maxB <= minS <= s[ii];
            MulMonoLeft(kk, b[jj], s[ii]);
            assert kk * b[jj] <= kk * s[ii];
          }
        }
      }
    }
  }
}

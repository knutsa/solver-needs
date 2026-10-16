ghost function Max(x: int, y: int): int {
  if x >= y then x else y
}

// The maximum number of games purchasable from costs c using bills a
// (in order). At each game, we may buy it (if the current bill covers
// the cost, consuming that bill) or skip it. This explores ALL valid
// purchasing strategies and returns the maximum count.
ghost function MaxPurchases(c: seq<int>, a: seq<int>): int
  decreases |c|
{
  if |c| == 0 || |a| == 0 then 0
  else if a[0] >= c[0] then
    Max(1 + MaxPurchases(c[1..], a[1..]), MaxPurchases(c[1..], a))
  else
    MaxPurchases(c[1..], a)
}

// MaxPurchases is bounded by both sequence lengths and is non-negative
lemma MaxPurchasesBound(c: seq<int>, a: seq<int>)
  ensures 0 <= MaxPurchases(c, a) <= |c|
  ensures MaxPurchases(c, a) <= |a|
  decreases |c|
{
  if |c| == 0 || |a| == 0 {
  } else if a[0] >= c[0] {
    MaxPurchasesBound(c[1..], a[1..]);
    MaxPurchasesBound(c[1..], a);
  } else {
    MaxPurchasesBound(c[1..], a);
  }
}

// More games available never decreases the maximum purchases
lemma MoreGamesNoWorse(c: seq<int>, a: seq<int>)
  requires |c| > 0
  ensures MaxPurchases(c, a) >= MaxPurchases(c[1..], a)
{
  if |a| == 0 {
  } else if a[0] >= c[0] {
    assert MaxPurchases(c, a) == Max(1 + MaxPurchases(c[1..], a[1..]), MaxPurchases(c[1..], a));
  } else {
  }
}

// One extra bill adds at most 1 to the number of purchases
lemma ExtraBillBounded(c: seq<int>, a: seq<int>)
  requires |a| > 0
  ensures MaxPurchases(c, a) <= MaxPurchases(c, a[1..]) + 1
  decreases |c|
{
  if |c| == 0 {
  } else {
    ExtraBillBounded(c[1..], a);
    MoreGamesNoWorse(c, a[1..]);
  }
}

// Greedy buying is optimal: when we can buy, it's always best to buy
lemma GreedyBuyOptimal(c: seq<int>, a: seq<int>)
  requires |c| > 0 && |a| > 0 && a[0] >= c[0]
  ensures MaxPurchases(c, a) == 1 + MaxPurchases(c[1..], a[1..])
{
  ExtraBillBounded(c[1..], a);
}

method GameShopping(c: seq<int>, a: seq<int>) returns (count: int)
  ensures count == MaxPurchases(c, a)
  ensures 0 <= count <= |c|
  ensures count <= |a|
{
  count := 0;
  var i := 0;
  var j := 0;

  while i < |c| && j < |a|
    invariant 0 <= i <= |c|
    invariant 0 <= j <= |a|
    invariant count >= 0
    invariant count + MaxPurchases(c[i..], a[j..]) == MaxPurchases(c, a)
  {
    if a[j] >= c[i] {
      GreedyBuyOptimal(c[i..], a[j..]);
      assert c[i..][1..] == c[(i+1)..];
      assert a[j..][1..] == a[(j+1)..];
      count := count + 1;
      j := j + 1;
    } else {
      assert c[i..][1..] == c[(i+1)..];
    }
    i := i + 1;
  }
  MaxPurchasesBound(c, a);
}

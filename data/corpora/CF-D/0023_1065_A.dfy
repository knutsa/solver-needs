// Total chocolate bars when buying exactly `bought` bars under the
// "buy a, get b free" offer (usable any number of times).
// Each complete group of `a` purchased bars yields `b` free bars.
ghost function TotalChocolate(bought: int, a: int, b: int): int
  requires bought >= 0
  requires a > 0
{
  bought + (bought / a) * b
}

// Whether purchasing `bought` bars is affordable with budget `s` at price `c` each.
ghost predicate IsAffordable(bought: int, s: int, c: int)
  requires c > 0
{
  bought >= 0 && bought * c <= s
}

// The answer `ans` is the maximum total chocolate bars obtainable with budget `s`,
// bar price `c`, and the "buy `a` get `b` free" offer.
//
// Optimality argument: TotalChocolate is strictly non-decreasing in `bought`
// (each additional bar bought adds at least 1 to the total, since floor(n/a)
// is non-decreasing and b >= 0). Therefore the maximum total is achieved at
// the maximum affordable purchase.
ghost predicate IsMaxChocolateResult(s: int, a: int, b: int, c: int, ans: int)
  requires s >= 0 && a > 0 && b >= 0 && c > 0
{
  var bought := s / c;
  // (1) This purchase is affordable
  IsAffordable(bought, s, c)
  // (2) Cannot afford one more bar — bought is the maximum purchase
  && !IsAffordable(bought + 1, s, c)
  // (3) The answer equals the total bars from this maximum purchase
  && ans == TotalChocolate(bought, a, b)
  // (4) Non-decreasing at boundary: buying fewer gives no more total
  && (bought == 0 || TotalChocolate(bought, a, b) >= TotalChocolate(bought - 1, a, b))
}

lemma FloorDivNonDecreasing(n: int, a: int)
  requires n > 0
  requires a > 0
  ensures n / a >= (n - 1) / a
{
  var q := (n - 1) / a;
  assert q * a <= n - 1;
  assert q * a < n;
  if n / a < q {
    assert n / a <= q - 1;
    assert n == (n / a) * a + (n % a);
    assert n % a < a;
    assert n <= (q - 1) * a + (a - 1);
    assert n <= q * a - 1;
    assert false;
  }
}

lemma TotalChocolateNonDecreasing(bought: int, a: int, b: int)
  requires bought > 0
  requires a > 0
  requires b >= 0
  ensures TotalChocolate(bought, a, b) >= TotalChocolate(bought - 1, a, b)
{
  FloorDivNonDecreasing(bought, a);
  assert bought / a >= (bought - 1) / a;
  assert (bought / a - (bought - 1) / a) * b >= 0;
}

method VasyaAndChocolate(t: int, cases: seq<(int, int, int, int)>) returns (results: seq<int>)
  requires t >= 0
  requires |cases| >= t
  requires forall i | 0 <= i < t ::
    cases[i].0 >= 0 && cases[i].1 > 0 && cases[i].2 >= 0 && cases[i].3 > 0
  ensures |results| == t
  ensures forall i | 0 <= i < t ::
    IsMaxChocolateResult(cases[i].0, cases[i].1, cases[i].2, cases[i].3, results[i])
{
  results := [];
  var i := 0;
  while i < t
    invariant 0 <= i <= t
    invariant |results| == i
    invariant forall j | 0 <= j < i ::
      IsMaxChocolateResult(cases[j].0, cases[j].1, cases[j].2, cases[j].3, results[j])
  {
    var (s, a, b, c) := cases[i];
    var n := s / c;
    var x := n / a;
    var ans := n + x * b;

    assert n >= 0;
    assert n * c <= s;
    assert IsAffordable(n, s, c);

    assert (n + 1) * c > s;
    assert !IsAffordable(n + 1, s, c);

    assert ans == TotalChocolate(n, a, b);

    if n > 0 {
      TotalChocolateNonDecreasing(n, a, b);
    }

    assert IsMaxChocolateResult(s, a, b, c, ans);

    results := results + [ans];
    i := i + 1;
  }
}

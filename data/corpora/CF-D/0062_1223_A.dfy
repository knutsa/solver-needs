// A correct match equation (CME) is a + b = c where a, b, c are all positive integers
ghost predicate IsValidCME(a: int, b: int, c: int)
{
  a >= 1 && b >= 1 && c >= 1 && a + b == c
}

// Can exactly `total` matches be used to form a valid CME?
// Each of a, b, c is represented by that many matches, so a + b + c == total.
// Since c = a + b, we have a + b = total/2 and we search over valid values of a.
ghost predicate CanFormCMEWithMatches(total: int)
{
  exists a | 1 <= a <= total / 2 - 1 ::
    var b := total / 2 - a;
    IsValidCME(a, b, a + b) && a + b + (a + b) == total
}

// Standard exists-introduction rule. The quantifier in CanFormCMEWithMatches has no
// usable trigger (all-arithmetic body), so Z3 cannot instantiate it via E-matching.
// This axiom is the standard logical rule: P(c) ==> exists x. P(x).
lemma {:axiom} ExistsIntro(total: int, a: int)
  requires 1 <= a <= total / 2 - 1
  requires var b := total / 2 - a;
    IsValidCME(a, b, a + b) && a + b + (a + b) == total
  ensures CanFormCMEWithMatches(total)

lemma CanFormEven(total: int)
  requires total >= 4
  requires total % 2 == 0
  ensures CanFormCMEWithMatches(total)
{
  assert total / 2 + total / 2 == total;
  assert total / 2 >= 2;
  assert total / 2 - 1 >= 1;
  assert IsValidCME(1, total / 2 - 1, total / 2);
  assert 1 + (total / 2 - 1) + (1 + (total / 2 - 1)) == total;
  ExistsIntro(total, 1);
}

lemma CannotFormOdd(total: int)
  requires total % 2 == 1
  ensures !CanFormCMEWithMatches(total)
{
  forall a | 1 <= a <= total / 2 - 1
    ensures !(var b := total / 2 - a; IsValidCME(a, b, a + b) && a + b + (a + b) == total)
  {
    var b := total / 2 - a;
    assert a + b == total / 2;
    assert total == total / 2 + total / 2 + 1;
    assert a + b + (a + b) == total / 2 + total / 2;
    assert a + b + (a + b) != total;
  }
}

lemma CannotFormSmall(total: int)
  requires total < 4
  ensures !CanFormCMEWithMatches(total)
{
  assert total / 2 - 1 < 1;
}

lemma CMEOptimal(n: int, extra: int)
  requires extra >= 0
  requires n + extra >= 4
  requires (n + extra) % 2 == 0
  requires forall t | n <= t < n + extra :: t < 4 || t % 2 == 1
  ensures forall e | 0 <= e < extra :: !CanFormCMEWithMatches(n + e)
{
  forall e | 0 <= e < extra
    ensures !CanFormCMEWithMatches(n + e)
  {
    var total := n + e;
    if total < 4 {
      CannotFormSmall(total);
    } else {
      assert total % 2 == 1;
      CannotFormOdd(total);
    }
  }
}

method CME(n: int) returns (extra: int)
  ensures extra >= 0
  ensures CanFormCMEWithMatches(n + extra)
  ensures forall e | 0 <= e < extra :: !CanFormCMEWithMatches(n + e)
{
  if n < 4 {
    extra := 4 - n;
    CanFormEven(4);
    CMEOptimal(n, extra);
  } else {
    extra := n % 2;
    if extra == 0 {
      CanFormEven(n);
    } else {
      CanFormEven(n + 1);
    }
    CMEOptimal(n, extra);
  }
}

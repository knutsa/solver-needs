// --- Specification ---

ghost function Abs(n: int): nat {
  if n < 0 then -n else n
}

ghost predicate IsLuckyDigit(d: int) {
  d == 4 || d == 7
}

// Decimal digits of a positive number (most-significant first); 0 maps to [].
ghost function Digits(n: nat): seq<int>
  decreases n
{
  if n == 0 then []
  else Digits(n / 10) + [n % 10]
}

// Count of lucky digits in a sequence (slice-based recursion).
ghost function CountLucky(s: seq<int>): nat
  decreases |s|
{
  if |s| == 0 then 0
  else CountLucky(s[..|s|-1]) + (if IsLuckyDigit(s[|s|-1]) then 1 else 0)
}

// A lucky number is a positive integer whose every digit is 4 or 7.
ghost predicate IsLuckyNumber(n: nat) {
  var d := Digits(n);
  n > 0 && forall i :: 0 <= i < |d| ==> IsLuckyDigit(d[i])
}

// A number is nearly lucky iff the count of lucky digits in its
// decimal representation is itself a lucky number.
ghost predicate IsNearlyLucky(n: int) {
  IsLuckyNumber(CountLucky(Digits(Abs(n))))
}

// --- Helper predicate and lemmas ---

// Bottom-up check: are all digits of n lucky?
ghost predicate AllDigitsLucky(n: nat)
  decreases n
{
  if n == 0 then true
  else IsLuckyDigit(n % 10) && AllDigitsLucky(n / 10)
}

// Decompose CountLucky(Digits(n)) by peeling off the last digit.
lemma CountLuckyDecompose(n: nat)
  requires n > 0
  ensures CountLucky(Digits(n)) == CountLucky(Digits(n / 10)) + (if IsLuckyDigit(n % 10) then 1 else 0)
{
  var d := Digits(n);
  assert d == Digits(n / 10) + [n % 10];
  assert d[..|d| - 1] == Digits(n / 10);
}

// AllDigitsLucky(n) <==> IsLuckyNumber(n) for n > 0.
lemma AllDigitsLuckyEquiv(n: nat)
  requires n > 0
  ensures AllDigitsLucky(n) <==> IsLuckyNumber(n)
  decreases n
{
  var d := Digits(n);
  if n / 10 == 0 {
    assert Digits(0) == [];
    assert d == Digits(0) + [n % 10] == [n % 10];
    assert |d| == 1;
    assert d[0] == n % 10;
    assert AllDigitsLucky(n) == IsLuckyDigit(n % 10);
    // For IsLuckyNumber: n > 0 && forall i :: 0 <= i < |d| ==> IsLuckyDigit(d[i])
    // |d| == 1, so the forall is just IsLuckyDigit(d[0]) == IsLuckyDigit(n%10)
    if IsLuckyDigit(n % 10) {
      assert IsLuckyDigit(d[0]);
      assert forall i :: 0 <= i < |d| ==> IsLuckyDigit(d[i]);
    }
  } else {
    AllDigitsLuckyEquiv(n / 10);
    var d' := Digits(n / 10);
    assert d == d' + [n % 10];
    if AllDigitsLucky(n) {
      forall i | 0 <= i < |d|
        ensures IsLuckyDigit(d[i])
      {
        if i < |d'| {
          assert d[i] == d'[i];
        } else {
          assert d[i] == n % 10;
        }
      }
    }
    if IsLuckyNumber(n) {
      assert IsLuckyDigit(d[|d| - 1]);
      assert d[|d| - 1] == n % 10;
      assert IsLuckyDigit(n % 10);
      forall i | 0 <= i < |d'|
        ensures IsLuckyDigit(d'[i])
      {
        assert d'[i] == d[i];
      }
      assert n / 10 > 0;
      assert IsLuckyNumber(n / 10);
      assert AllDigitsLucky(n / 10);
    }
  }
}

// --- Implementation ---

method NearlyLucky(n: int) returns (result: bool)
  ensures result == IsNearlyLucky(n)
{
  var num := if n < 0 then -n else n;
  assert num as nat == Abs(n);

  if num == 0 {
    result := false;
    return;
  }

  var count := 0;
  var temp := num;

  while temp > 0
    invariant temp >= 0
    invariant count >= 0
    invariant count + CountLucky(Digits(temp as nat)) == CountLucky(Digits(num as nat))
    decreases temp
  {
    CountLuckyDecompose(temp as nat);
    var digit := temp % 10;
    if digit == 4 || digit == 7 {
      count := count + 1;
    }
    temp := temp / 10;
  }

  assert count as nat == CountLucky(Digits(Abs(n)));

  if count == 0 {
    result := false;
    return;
  }

  var flag := true;
  temp := count;

  while temp > 0
    invariant temp >= 0
    invariant (flag && AllDigitsLucky(temp as nat)) <==> AllDigitsLucky(count as nat)
    decreases temp
  {
    var digit := temp % 10;
    if digit != 4 && digit != 7 {
      flag := false;
    }
    temp := temp / 10;
  }

  AllDigitsLuckyEquiv(count as nat);
  result := flag;
}

ghost predicate IsDigitChar(c: char)
{
  '0' <= c <= '9'
}

ghost predicate AllDigits(s: string)
{
  forall i | 0 <= i < |s| :: IsDigitChar(s[i])
}

ghost function DigitVal(c: char): int
  requires IsDigitChar(c)
{
  (c as int) - ('0' as int)
}

// The natural number represented by a non-empty digit string
ghost function StringToNat(s: string): int
  requires |s| > 0
  requires AllDigits(s)
  decreases |s|
{
  if |s| == 1 then DigitVal(s[0])
  else StringToNat(s[..|s|-1]) * 10 + DigitVal(s[|s|-1])
}

// Count how many substrings ending at the last position of s are even.
// Candidates: s[0..|s|], s[1..|s|], ..., s[|s|-1..|s|]
ghost function CountEvenEndingHere(s: string): int
  requires |s| > 0
  requires AllDigits(s)
  decreases |s|
{
  var thisOne := if StringToNat(s) % 2 == 0 then 1 else 0;
  if |s| == 1 then thisOne
  else thisOne + CountEvenEndingHere(s[1..])
}

// Total count of even substrings of s:
// |{ (l, r) | 0 <= l <= r < |s| && StringToNat(s[l..r+1]) % 2 == 0 }|
ghost function CountEvenSubstrings(s: string): int
  requires AllDigits(s)
  decreases |s|
{
  if |s| == 0 then 0
  else CountEvenSubstrings(s[..|s|-1]) + CountEvenEndingHere(s)
}

// A number's parity depends only on its last digit
lemma ParityLemma(s: string)
  requires |s| > 0
  requires AllDigits(s)
  ensures StringToNat(s) % 2 == DigitVal(s[|s|-1]) % 2
  decreases |s|
{
  if |s| == 1 {
  } else {
    assert StringToNat(s) == StringToNat(s[..|s|-1]) * 10 + DigitVal(s[|s|-1]);
  }
}

// If last digit is even, all |s| substrings ending here are even; otherwise 0
lemma CountEvenEndingHereValue(s: string)
  requires |s| > 0
  requires AllDigits(s)
  ensures DigitVal(s[|s|-1]) % 2 == 0 ==> CountEvenEndingHere(s) == |s|
  ensures DigitVal(s[|s|-1]) % 2 != 0 ==> CountEvenEndingHere(s) == 0
  decreases |s|
{
  ParityLemma(s);
  if |s| == 1 {
  } else {
    assert s[1..][|s[1..]|-1] == s[|s|-1];
    CountEvenEndingHereValue(s[1..]);
  }
}

method EvenSubstrings(s: string) returns (count: int)
  requires AllDigits(s)
  ensures count == CountEvenSubstrings(s)
{
  count := 0;
  for i := 0 to |s|
    invariant count == CountEvenSubstrings(s[..i])
  {
    assert s[..i+1][..i] == s[..i];
    CountEvenEndingHereValue(s[..i+1]);
    assert s[..i+1][|s[..i+1]|-1] == s[i];
    if s[i] == '0' || s[i] == '2' || s[i] == '4' || s[i] == '6' || s[i] == '8' {
      count := count + i + 1;
    }
  }
  assert s[..|s|] == s;
}

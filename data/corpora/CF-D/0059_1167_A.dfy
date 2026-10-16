// --- Formal specification predicates ---

ghost predicate IsDigit(c: char)
{
  '0' <= c <= '9'
}

// A telephone number is exactly 11 digits where the first digit is '8'.
ghost predicate IsPhoneNumber(t: seq<char>)
{
  |t| == 11 && t[0] == '8' && (forall i | 0 <= i < |t| :: IsDigit(t[i]))
}

// `sub` can be obtained from `s` by deleting zero or more characters (preserving order).
ghost predicate IsSubsequence(sub: seq<char>, s: seq<char>)
  decreases |s|
{
  if |sub| == 0 then true
  else if |s| == 0 then false
  else
    // Either match sub[0] with s[0] and advance both, or skip s[0]
    (sub[0] == s[0] && IsSubsequence(sub[1..], s[1..]))
    || IsSubsequence(sub, s[1..])
}

// Compilable equivalent of: exists t :: IsPhoneNumber(t) && IsSubsequence(t, s).
// Enumerates all ways to select `remaining` characters from s in order;
// the first selected character must be '8', and every selected character must be a digit.
ghost predicate CanFormPhone(s: seq<char>, remaining: nat)
  decreases |s|
{
  if remaining == 0 then true
  else if |s| == 0 then false
  else
    // Skip s[0]
    CanFormPhone(s[1..], remaining)
    ||
    // Select s[0] as the next phone-number digit
    (IsDigit(s[0]) && (remaining == 11 ==> s[0] == '8') && CanFormPhone(s[1..], remaining - 1))
}

// --- Helper lemmas ---

// When we have enough digits and remaining <= 10, we can always form the phone suffix.
lemma CanFormPhoneAllDigits(t: seq<char>, r: nat)
  requires r <= 10
  requires |t| >= r
  requires forall i | 0 <= i < |t| :: IsDigit(t[i])
  ensures CanFormPhone(t, r)
  decreases |t|
{
  if r == 0 {
  } else {
    CanFormPhoneAllDigits(t[1..], r - 1);
  }
}

// If the first character is not '8', it cannot start a phone number,
// so CanFormPhone(t, 11) reduces to skipping it.
lemma CanFormPhoneSkipNon8(t: seq<char>)
  requires |t| >= 11
  requires forall i | 0 <= i < |t| :: IsDigit(t[i])
  requires t[0] != '8'
  ensures CanFormPhone(t, 11) == CanFormPhone(t[1..], 11)
{
}

// If the first character is '8' and we have >= 11 characters (all digits),
// we can form a phone number.
lemma CanFormPhoneFound8(t: seq<char>)
  requires |t| >= 11
  requires forall i | 0 <= i < |t| :: IsDigit(t[i])
  requires t[0] == '8'
  ensures CanFormPhone(t, 11)
{
  CanFormPhoneAllDigits(t[1..], 10);
}

// If the sequence is shorter than remaining, we cannot form a phone number.
lemma CanFormPhoneTooShort(t: seq<char>, r: nat)
  requires |t| < r
  requires r > 0
  ensures !CanFormPhone(t, r)
  decreases |t|
{
  if |t| == 0 {
  } else {
    CanFormPhoneTooShort(t[1..], r);
    CanFormPhoneTooShort(t[1..], r - 1);
  }
}

// --- Method with specification ---

method TelephoneNumber(s: string, n: int) returns (result: bool)
  requires n == |s|
  requires forall i | 0 <= i < n :: IsDigit(s[i])
  ensures result == CanFormPhone(s, 11)
{
  assert s[0..] == s;
  var i := 0;
  while i < n - 10
    invariant 0 <= i <= n
    invariant CanFormPhone(s, 11) == CanFormPhone(s[i..], 11)
  {
    assert |s[i..]| >= 11;
    if s[i] == '8' {
      CanFormPhoneFound8(s[i..]);
      return true;
    }
    CanFormPhoneSkipNon8(s[i..]);
    assert s[i..][1..] == s[i+1..];
    i := i + 1;
  }
  CanFormPhoneTooShort(s[i..], 11);
  return false;
}

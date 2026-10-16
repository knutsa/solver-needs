// Count occurrences of value v in sequence s
ghost function CountOccurrences(s: seq<int>, v: int): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == v then 1 else 0) + CountOccurrences(s[..|s|-1], v)
}

// Formalizes the problem statement: a valid assignment of cards to k phone numbers.
// assignment[i] == 0 means card i is unused.
// assignment[i] == j (1 <= j <= k) means card i belongs to phone number j.
// Each phone number uses exactly 11 cards, at least one of which has digit 8
// (capturing: phone numbers have length 11 and start with 8).
ghost predicate ValidPhoneAssignment(assignment: seq<int>, k: int, digits: seq<int>)
{
  |assignment| == |digits| &&
  k >= 0 &&
  (forall i | 0 <= i < |assignment| :: 0 <= assignment[i] <= k) &&
  (forall j | 1 <= j <= k ::
    CountOccurrences(assignment, j) == 11 &&
    (exists i | 0 <= i < |digits| :: assignment[i] == j && digits[i] == 8))
}

// Necessary and sufficient condition for forming k phone numbers from the cards:
//   - Each phone number requires 11 cards  =>  11 * k <= |digits|
//   - Each phone number requires at least one 8  =>  k <= count of 8s
ghost predicate Achievable(k: int, digits: seq<int>)
{
  k >= 0 && 11 * k <= |digits| && k <= CountOccurrences(digits, 8)
}

lemma CountOccurrencesNonNeg(s: seq<int>, v: int)
  ensures CountOccurrences(s, v) >= 0
  decreases |s|
{
  if |s| > 0 {
    CountOccurrencesNonNeg(s[..|s|-1], v);
  }
}

method PhoneNumbers(n: int, digits: seq<int>) returns (count: int)
  requires n == |digits|
  ensures Achievable(count, digits)
  ensures !Achievable(count + 1, digits)
{
  var cnt8 := 0;
  for i := 0 to |digits|
    invariant cnt8 == CountOccurrences(digits[..i], 8)
  {
    assert digits[..i+1] == digits[..i] + [digits[i]];
    if digits[i] == 8 {
      cnt8 := cnt8 + 1;
    }
  }
  assert digits[..|digits|] == digits;
  CountOccurrencesNonNeg(digits, 8);
  if cnt8 < n / 11 {
    count := cnt8;
  } else {
    count := n / 11;
  }
}

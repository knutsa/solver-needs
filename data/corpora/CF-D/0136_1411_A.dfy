// Count the consecutive ')' characters at the end of the string.
// This is the mathematical definition of the problem's core concept:
// "the number of characters ')' at the end of the string."
ghost function TrailingParens(s: string): nat
  decreases |s|
{
  if |s| == 0 then 0
  else if s[|s| - 1] == ')' then 1 + TrailingParens(s[..|s| - 1])
  else 0
}

// A message is bad if the trailing ')' count strictly exceeds
// the number of remaining (non-trailing) characters.
ghost predicate IsBad(s: string)
{
  TrailingParens(s) > |s| - TrailingParens(s)
}

method InGameChat(s: string) returns (bad: bool)
  ensures bad == IsBad(s)
{
  var i := |s| - 1;
  assert s[..|s|] == s;
  while i >= 0 && s[i] == ')'
    invariant -1 <= i <= |s| - 1
    invariant TrailingParens(s) == (|s| - 1 - i) + TrailingParens(s[..i + 1])
  {
    assert s[..i + 1][..i] == s[..i];
    i := i - 1;
  }
  assert TrailingParens(s[..i + 1]) == 0;
  var x := |s| - i - 1;
  bad := x > |s| - x;
}

// Count the number of 'a' characters in a string
ghost function CountA(s: string): nat
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[|s|-1] == 'a' then 1 else 0) + CountA(s[..|s|-1])
}

// Can we form a "good" subsequence of exactly `len` characters from `s`?
// A good string has strictly more than half its characters equal to 'a'.
// We choose numA of the available 'a's and (len - numA) of the available non-'a's,
// such that 2 * numA > len (the "good" condition).
ghost predicate CanFormGoodOfLength(s: string, len: int)
{
  0 <= len <= |s| &&
  exists numA: int | 0 <= numA <= len ::
    numA <= CountA(s) &&
    len - numA + CountA(s) <= |s| &&
    2 * numA > len
}

lemma CountABound(s: string)
  ensures CountA(s) <= |s|
  decreases |s|
{
  if |s| > 0 {
    CountABound(s[..|s|-1]);
  }
}

method LoveA(s: string) returns (result: int)
  requires CountA(s) >= 1
  ensures 0 <= result <= |s|
  ensures CanFormGoodOfLength(s, result)
  ensures forall k | result < k <= |s| :: !CanFormGoodOfLength(s, k)
{
  CountABound(s);

  var count := 0;
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant count == CountA(s[..i])
  {
    assert s[..i+1][..i] == s[..i];
    if s[i] == 'a' {
      count := count + 1;
    }
    i := i + 1;
  }
  assert s[..|s|] == s;
  assert count == CountA(s);

  var candidate := 2 * count - 1;
  if |s| < candidate {
    result := |s|;
    // Witness for CanFormGoodOfLength: numA = count
    assert 0 <= count <= |s|;
    assert count <= CountA(s);
    assert |s| - count + CountA(s) <= |s|;
    assert 2 * count > |s|;
    // Maximality: range result < k <= |s| is empty since result == |s|
  } else {
    result := candidate;
    // Witness for CanFormGoodOfLength: numA = count
    assert 0 <= count <= candidate;
    assert count <= CountA(s);
    assert candidate - count + CountA(s) <= |s|;
    assert 2 * count > candidate;

    // Prove maximality: for k > 2*count-1, any numA with 2*numA > k
    // requires numA > count = CountA(s), contradicting numA <= CountA(s)
    forall k | candidate < k <= |s|
      ensures !CanFormGoodOfLength(s, k)
    {
      assert k >= 2 * count;
      assert forall numA: int | 0 <= numA <= k && numA <= CountA(s) ::
        2 * numA <= k;
    }
  }
}

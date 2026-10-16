// Bob's encoding: concatenate all length-2 substrings of a, left to right.
// E.g., BobEncode("abac") == "ab" + "ba" + "ac" == "abbaac"
ghost function BobEncode(a: string): string
  requires |a| >= 2
  decreases |a|
{
  if |a| == 2 then a
  else a[0..2] + BobEncode(a[1..])
}

lemma BobEncodeInverse(a: string, b: string)
  requires |a| >= 2
  requires |b| == 2 * (|a| - 1)
  requires a[0] == b[0]
  requires forall j :: 1 <= j < |a| ==> a[j] == b[2 * j - 1]
  requires forall k :: 1 <= k < |a| - 1 ==> b[2 * k] == b[2 * k - 1]
  ensures BobEncode(a) == b
  decreases |a|
{
  if |a| == 2 {
    assert a[1] == b[1];
  } else {
    var a' := a[1..];
    var b' := b[2..];

    // a'[0] == b'[0] via overlap
    assert a[1] == b[1];
    assert b[2] == b[1];
    assert a'[0] == b'[0];

    // Index mapping for recursive call
    forall j | 1 <= j < |a'|
      ensures a'[j] == b'[2 * j - 1]
    {
      assert a'[j] == a[j + 1] == b[2 * (j + 1) - 1];
      assert b'[2 * j - 1] == b[2 * j + 1];
    }

    // Overlap property for b'
    forall k | 1 <= k < |a'| - 1
      ensures b'[2 * k] == b'[2 * k - 1]
    {
      assert b'[2 * k] == b[2 * (k + 1)];
      assert b'[2 * k - 1] == b[2 * (k + 1) - 1];
    }

    BobEncodeInverse(a', b');

    assert a[0..2] == [a[0], a[1]];
    assert a[0..2] == [b[0], b[1]];
    assert b == b[..2] + b[2..];
  }
}

method ShortSubstrings(b: string) returns (a: string)
  requires |b| >= 2
  requires |b| % 2 == 0
  // Valid Bob encoding: overlapping characters must match
  requires forall k :: 1 <= k < |b| / 2 ==> b[2 * k] == b[2 * k - 1]
  ensures |a| >= 2
  ensures BobEncode(a) == b
{
  var partial: string := "";
  var i := 1;
  while i < |b|
    invariant 1 <= i <= |b| + 1
    invariant i % 2 == 1
    invariant |partial| == (i - 1) / 2
    invariant forall j :: 0 <= j < |partial| ==> partial[j] == b[2 * j + 1]
  {
    partial := partial + [b[i]];
    i := i + 2;
  }

  a := [b[0]] + partial;

  forall j | 1 <= j < |a|
    ensures a[j] == b[2 * j - 1]
  {
    assert a[j] == partial[j - 1] == b[2 * (j - 1) + 1];
  }

  BobEncodeInverse(a, b);
}

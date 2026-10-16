// The Right-Left encryption: builds a string by writing s[0], then alternately
// appending (odd indices) and prepending (even indices >= 2) each subsequent character.
ghost function Encrypt(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else if |s| == 1 then [s[0]]
  else if |s| % 2 == 0 then
    // Last character index is odd → append to the right
    Encrypt(s[..|s|-1]) + [s[|s|-1]]
  else
    // Last character index is even (>=2) → prepend to the left
    [s[|s|-1]] + Encrypt(s[..|s|-1])
}

// s is a valid decryption of ciphertext t iff encrypting s produces t
ghost predicate IsDecryptionOf(s: string, t: string)
{
  |s| == |t| && Encrypt(s) == t
}

lemma {:induction false} EncryptAppendEven(s: string, c: char)
  requires |s| >= 1
  requires |s| % 2 == 1
  ensures Encrypt(s + [c]) == Encrypt(s) + [c]
{
  assert (s + [c])[..|s|] == s;
}

lemma {:induction false} EncryptAppendOdd(s: string, c: char)
  requires |s| >= 2
  requires |s| % 2 == 0
  ensures Encrypt(s + [c]) == [c] + Encrypt(s)
{
  assert (s + [c])[..|s|] == s;
}

lemma SliceConcat(t: string, lo: int, hi: int)
  requires 0 <= lo < hi <= |t|
  ensures t[lo..hi] == [t[lo]] + t[lo + 1..hi]
{}

lemma SliceAppend(t: string, lo: int, hi: int)
  requires 0 <= lo < hi <= |t|
  ensures t[lo..hi] == t[lo..hi - 1] + [t[hi - 1]]
{}

method {:vcs_split_on_every_assert} Decrypt(t: string) returns (s: string)
  ensures IsDecryptionOf(s, t)
{
  var n := |t|;
  if n == 0 {
    s := "";
    return;
  }
  var mid := (n - 1) / 2;
  s := [t[mid]];
  var u1: int := mid + 1;
  var u2: int := mid - 1;

  while u1 < n && u2 >= 0
    invariant -1 <= u2
    invariant u1 <= n
    invariant u2 + 1 <= u1
    invariant |s| == u1 - u2 - 1
    invariant |s| % 2 == 1
    invariant u1 + u2 == 2 * mid
    invariant Encrypt(s) == t[u2 + 1..u1]
    decreases u2 + 1
  {
    ghost var old_u1 := u1;
    ghost var old_u2 := u2;
    ghost var old_enc := Encrypt(s);

    EncryptAppendEven(s, t[u1]);
    s := s + [t[u1]];
    assert Encrypt(s) == old_enc + [t[old_u1]];

    ghost var mid_enc := Encrypt(s);
    EncryptAppendOdd(s, t[u2]);
    s := s + [t[u2]];
    assert Encrypt(s) == [t[old_u2]] + mid_enc;

    SliceAppend(t, old_u2 + 1, old_u1 + 1);
    assert t[old_u2 + 1..old_u1 + 1] == t[old_u2 + 1..old_u1] + [t[old_u1]];
    assert mid_enc == t[old_u2 + 1..old_u1 + 1];

    SliceConcat(t, old_u2, old_u1 + 1);
    assert t[old_u2..old_u1 + 1] == [t[old_u2]] + t[old_u2 + 1..old_u1 + 1];
    assert Encrypt(s) == t[old_u2..old_u1 + 1];

    u1 := u1 + 1;
    u2 := u2 - 1;
  }

  // After loop: u2 == -1, so Encrypt(s) == t[0..u1]
  assert u2 == -1;

  if n % 2 == 0 {
    assert u1 == n - 1;
    assert Encrypt(s) == t[0..n - 1];
    EncryptAppendEven(s, t[n - 1]);
    s := s + [t[n - 1]];
    // Encrypt(s) == t[0..n-1] + [t[n-1]]
    SliceAppend(t, 0, n);
    assert t[0..n] == t[0..n - 1] + [t[n - 1]];
    assert Encrypt(s) == t[0..n];
  } else {
    assert u1 == n;
    assert Encrypt(s) == t[0..n];
  }

  assert t[0..n] == t;
  assert |s| == n;
  assert Encrypt(s) == t;
}

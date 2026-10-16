ghost function TriNum(k: nat): nat
{
  k * (k + 1) / 2
}

ghost function Repeat(c: char, count: nat): string
  decreases count
{
  if count == 0 then ""
  else [c] + Repeat(c, count - 1)
}

// Encryption per the problem: write s[0] once, s[1] twice, ..., s[m-1] m times
ghost function Encrypt(s: string): string
  decreases |s|
{
  if |s| == 0 then ""
  else Encrypt(s[..|s|-1]) + Repeat(s[|s|-1], |s|)
}

// t is a valid encryption: its length is triangular and each group is uniform
ghost predicate IsValidEncryption(t: string)
{
  exists m: nat ::
    TriNum(m) == |t| &&
    forall i | 0 <= i < m ::
      forall j | TriNum(i) <= j < TriNum(i + 1) ::
        t[j] == t[TriNum(i)]
}

// 2 * TriNum(k) == k * (k + 1), avoiding division issues
lemma TwoTimesTriNum(k: nat)
  ensures 2 * TriNum(k) == k * (k + 1)
{
  if k % 2 == 0 {
    assert k == 2 * (k / 2);
  } else {
    assert k + 1 == 2 * ((k + 1) / 2);
  }
}

// TriNum(k+1) == TriNum(k) + (k+1)
lemma TriNumSucc(k: nat)
  ensures TriNum(k + 1) == TriNum(k) + (k + 1)
{
  TwoTimesTriNum(k);
  TwoTimesTriNum(k + 1);
  assert (k + 1) * (k + 2) == k * (k + 1) + 2 * (k + 1);
  assert 2 * TriNum(k + 1) == 2 * (TriNum(k) + (k + 1));
}

// TriNum is weakly monotonic
lemma TriNumLeq(a: nat, b: nat)
  requires a <= b
  ensures TriNum(a) <= TriNum(b)
  decreases b - a
{
  if a < b {
    TriNumLeq(a, b - 1);
    TriNumSucc(b - 1);
  }
}

// Encrypt(s ++ [c]) == Encrypt(s) ++ Repeat(c, |s|+1)
lemma EncryptAppend(s: string, c: char)
  ensures Encrypt(s + [c]) == Encrypt(s) + Repeat(c, |s| + 1)
{
  var s' := s + [c];
  assert s'[..|s'| - 1] == s;
}

// A uniform slice of t equals Repeat
lemma UniformSliceIsRepeat(t: string, start: nat, len: nat, c: char)
  requires start + len <= |t|
  requires forall i | start <= i < start + len :: t[i] == c
  ensures t[start..start + len] == Repeat(c, len)
  decreases len
{
  if len > 0 {
    UniformSliceIsRepeat(t, start + 1, len - 1, c);
    assert t[start..start + len] == [t[start]] + t[start + 1..start + len];
  }
}

method DecryptRepeatingCipher(t: string, n: int) returns (s: string)
  requires n == |t|
  requires IsValidEncryption(t)
  ensures Encrypt(s) == t
{
  ghost var m: nat :| TriNum(m) == |t| &&
    forall i | 0 <= i < m ::
      forall j | TriNum(i) <= j < TriNum(i + 1) ::
        t[j] == t[TriNum(i)];

  s := "";
  var x := 0;
  var y := 1;

  while x < n
    invariant y >= 1
    invariant |s| == y - 1
    invariant x == TriNum(y - 1)
    invariant y - 1 <= m
    invariant x <= |t|
    invariant Encrypt(s) == t[..x]
  {
    ghost var k: nat := y - 1;

    // k < m: otherwise x == TriNum(m) == |t| == n, contradicting loop guard
    assert k < m by {
      if k == m { assert x == TriNum(m) == |t|; }
    }

    TriNumSucc(k);
    TriNumLeq(k + 1, m);

    // Group k is uniform and fits within t
    assert forall j | x <= j < x + y :: t[j] == t[x];
    UniformSliceIsRepeat(t, x, y, t[x]);

    // Connect Encrypt(s + [t[x]]) to t[..x+y]
    EncryptAppend(s, t[x]);
    assert t[..x] + t[x..x + y] == t[..x + y];

    s := s + [t[x]];
    x := x + y;
    y := y + 1;
  }

  assert t[..|t|] == t;
}

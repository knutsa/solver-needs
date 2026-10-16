// Count occurrences of character c in sequence t
ghost function CountChar(c: char, t: seq<char>): nat
  decreases |t|
{
  if |t| == 0 then 0
  else CountChar(c, t[..|t|-1]) + (if t[|t|-1] == c then 1 else 0)
}

// t is a subsequence of s (derivable by deleting symbols without reordering)
ghost predicate IsSubsequence(t: seq<char>, s: seq<char>)
  decreases |s| + |t|
{
  if |t| == 0 then true
  else if |s| == 0 then false
  else if t[|t|-1] == s[|s|-1] then IsSubsequence(t[..|t|-1], s[..|s|-1])
  else IsSubsequence(t, s[..|s|-1])
}

// A sequence is "good" w.r.t. k: each of the first k letters occurs equally often
ghost predicate IsGood(t: seq<char>, k: int)
  requires 1 <= k <= 26
{
  forall i | 0 <= i < k ::
    CountChar(('A' as int + i) as char, t) == CountChar('A', t)
}

// Each of the first k letters appears at least m times in s.
// Under the constraint that s contains only the first k letters, this is
// equivalent to the existence of a good subsequence of length m * k:
// one can always select m occurrences of each required letter in order.
ghost predicate HasAtLeastMOfEach(s: seq<char>, k: int, m: int)
  requires 1 <= k <= 26
{
  forall i | 0 <= i < k :: CountChar(('A' as int + i) as char, s) >= m
}

lemma MulDivK(a: int, b: int)
  requires a >= 0
  requires b >= 1
  ensures (a * b) / b == a
  ensures (a * b) % b == 0
{}

// Wrapper function to provide a trigger for the triggerless quantifier
ghost function CountIth(i: int, s: seq<char>): nat
  requires 0 <= i < 26
{
  CountChar(('A' as int + i) as char, s)
}

lemma CountIthDef(i: int, s: seq<char>)
  requires 0 <= i < 26
  ensures CountIth(i, s) == CountChar(('A' as int + i) as char, s)
{}

lemma HasAtLeastFromCountIth(s: seq<char>, k: int, m: int)
  requires 1 <= k <= 26
  requires forall i {:trigger CountIth(i, s)} | 0 <= i < k :: CountIth(i, s) >= m
  ensures HasAtLeastMOfEach(s, k, m)
{
  forall i | 0 <= i < k
    ensures CountChar(('A' as int + i) as char, s) >= m
  {
    CountIthDef(i, s);
    assert CountIth(i, s) >= m;
  }
}

lemma NotHasAtLeastFromCountIth(s: seq<char>, k: int, m: int, wit: int)
  requires 1 <= k <= 26
  requires 0 <= wit < k
  requires CountIth(wit, s) < m
  ensures !HasAtLeastMOfEach(s, k, m)
{
  CountIthDef(wit, s);
  assert CountChar(('A' as int + wit) as char, s) < m;
}

method LongestGoodSubsequence(s: seq<char>, k: int) returns (length: int)
  requires 1 <= k <= 26
  requires forall i | 0 <= i < |s| :: 'A' <= s[i] && s[i] <= (('A' as int + k - 1) as char)
  ensures length >= 0
  ensures length % k == 0
  ensures HasAtLeastMOfEach(s, k, length / k)
  ensures forall m | length / k < m && m <= |s| :: !HasAtLeastMOfEach(s, k, m)
{
  var upper: seq<char> := [];
  var i := 0;
  var limit := if k < 26 then k else 26;
  while i < limit
    invariant 0 <= i <= limit
    invariant limit == k
    invariant |upper| == i
    invariant forall j | 0 <= j < i :: upper[j] == ('A' as int + j) as char
  {
    upper := upper + [('A' as int + i) as char];
    i := i + 1;
  }

  assert |upper| == k;

  if |upper| == 0 {
    length := 0;
    return;
  }

  var counts: seq<int> := [];
  i := 0;
  while i < |upper|
    invariant 0 <= i <= |upper|
    invariant |upper| == k
    invariant |counts| == i
    invariant forall j | 0 <= j < i :: counts[j] == CountChar(upper[j], s)
  {
    var count := 0;
    var j := 0;
    while j < |s|
      invariant 0 <= j <= |s|
      invariant count == CountChar(upper[i], s[..j])
    {
      assert s[..j+1][..j] == s[..j];
      if s[j] == upper[i] {
        count := count + 1;
      }
      j := j + 1;
    }
    assert s[..|s|] == s;
    counts := counts + [count];
    i := i + 1;
  }

  assert |counts| == k;

  var minCount := counts[0];
  ghost var minIdx := 0;
  i := 1;
  while i < |counts|
    invariant 1 <= i <= |counts|
    invariant 0 <= minIdx < i
    invariant minCount == counts[minIdx]
    invariant forall j | 0 <= j < i :: minCount <= counts[j]
  {
    if counts[i] < minCount {
      minCount := counts[i];
      minIdx := i;
    }
    i := i + 1;
  }

  assert counts[minIdx] == CountChar(upper[minIdx], s);
  assert minCount >= 0;

  MulDivK(minCount, k);
  length := minCount * k;
  assert length / k == minCount;

  // Postcondition 3: use CountIth wrapper for trigger
  forall ii {:trigger CountIth(ii, s)} | 0 <= ii < k
    ensures CountIth(ii, s) >= length / k
  {
    assert upper[ii] == ('A' as int + ii) as char;
    assert counts[ii] == CountChar(upper[ii], s);
    CountIthDef(ii, s);
    assert minCount <= counts[ii];
  }
  HasAtLeastFromCountIth(s, k, length / k);

  // Postcondition 4
  assert upper[minIdx] == ('A' as int + minIdx) as char;
  assert counts[minIdx] == CountChar(upper[minIdx], s);
  CountIthDef(minIdx, s);
  assert CountIth(minIdx, s) == minCount;

  forall m | length / k < m && m <= |s|
    ensures !HasAtLeastMOfEach(s, k, m)
  {
    NotHasAtLeastFromCountIth(s, k, m, minIdx);
  }
}

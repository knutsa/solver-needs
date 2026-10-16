ghost predicate ValidAB(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'a' || s[i] == 'b'
}

ghost function CountChar(s: seq<char>, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

ghost predicate BalancedPrefixes(s: seq<char>)
{
  forall k | 1 <= k <= |s| / 2 :: CountChar(s[..2 * k], 'a') == CountChar(s[..2 * k], 'b')
}

ghost function HammingDist(s: seq<char>, t: seq<char>): int
  requires |s| == |t|
  decreases |s|
{
  if |s| == 0 then 0
  else HammingDist(s[..|s|-1], t[..|t|-1]) + (if s[|s|-1] != t[|s|-1] then 1 else 0)
}

// Counts consecutive pairs where both characters are the same.
// Each such pair requires at least one replacement to become balanced,
// and one replacement always suffices, so this equals the minimum ops.
ghost function CountBadPairs(s: seq<char>): int
  requires |s| % 2 == 0
  decreases |s|
{
  if |s| == 0 then 0
  else CountBadPairs(s[..|s|-2]) + (if s[|s|-2] == s[|s|-1] then 1 else 0)
}

lemma CountCharAppend(s: seq<char>, c: char, ch: char)
  ensures CountChar(s + [c], ch) == CountChar(s, ch) + (if c == ch then 1 else 0)
{
  assert (s + [c])[..|s|] == s;
}

lemma CountCharAppend2(s: seq<char>, a: char, b: char, ch: char)
  ensures CountChar(s + [a, b], ch) == CountChar(s, ch) + (if a == ch then 1 else 0) + (if b == ch then 1 else 0)
{
  assert s + [a, b] == (s + [a]) + [b];
  CountCharAppend(s + [a], b, ch);
  CountCharAppend(s, a, ch);
}

lemma HammingDistAppend2(s1: seq<char>, s2: seq<char>, a1: char, a2: char, b1: char, b2: char)
  requires |s1| == |s2|
  ensures HammingDist(s1 + [a1, a2], s2 + [b1, b2]) == HammingDist(s1, s2) + (if a1 != b1 then 1 else 0) + (if a2 != b2 then 1 else 0)
{
  var sa := s1 + [a1, a2];
  var sb := s2 + [b1, b2];
  assert sa[..|sa|-1] == s1 + [a1];
  assert sb[..|sb|-1] == s2 + [b1];
  assert (s1 + [a1])[..|s1|] == s1;
  assert (s2 + [b1])[..|s2|] == s2;
}

lemma CountBadPairsStep(s: seq<char>, a: char, b: char)
  requires |s| % 2 == 0
  ensures |s + [a, b]| % 2 == 0
  ensures CountBadPairs(s + [a, b]) == CountBadPairs(s) + (if a == b then 1 else 0)
{
  var s' := s + [a, b];
  assert s'[..|s'|-2] == s;
}

lemma BalancedPrefixesExtend(result: seq<char>, a: char, b: char)
  requires |result| % 2 == 0
  requires BalancedPrefixes(result)
  requires CountChar(result, 'a') == CountChar(result, 'b')
  requires (a == 'a' && b == 'b') || (a == 'b' && b == 'a')
  ensures BalancedPrefixes(result + [a, b])
{
  var r := result + [a, b];
  CountCharAppend2(result, a, b, 'a');
  CountCharAppend2(result, a, b, 'b');
  forall k | 1 <= k <= |r| / 2
    ensures CountChar(r[..2*k], 'a') == CountChar(r[..2*k], 'b')
  {
    if 2*k <= |result| {
      assert r[..2*k] == result[..2*k];
    } else {
      assert 2*k == |r|;
      assert r[..2*k] == r;
    }
  }
}

method Prefixes(s: seq<char>) returns (ops: int, result: seq<char>)
  requires |s| % 2 == 0
  requires ValidAB(s)
  ensures |result| == |s|
  ensures ValidAB(result)
  ensures BalancedPrefixes(result)
  ensures ops == HammingDist(s, result)
  ensures ops == CountBadPairs(s)
{
  ops := 0;
  result := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant i % 2 == 0
    invariant |result| == i
    invariant ValidAB(result)
    invariant ops == CountBadPairs(s[..i])
    invariant CountChar(result, 'a') == i / 2
    invariant CountChar(result, 'b') == i / 2
    invariant BalancedPrefixes(result)
    invariant ops == HammingDist(s[..i], result)
  {
    var a: char, b: char;
    if s[i] == s[i + 1] {
      a := 'a';
      b := 'b';
      ops := ops + 1;
    } else {
      a := s[i];
      b := s[i + 1];
    }

    assert s[..i] + [s[i], s[i + 1]] == s[..i + 2];

    CountBadPairsStep(s[..i], s[i], s[i + 1]);
    HammingDistAppend2(s[..i], result, s[i], s[i + 1], a, b);
    CountCharAppend2(result, a, b, 'a');
    CountCharAppend2(result, a, b, 'b');
    BalancedPrefixesExtend(result, a, b);

    result := result + [a, b];
    i := i + 2;
  }

  assert s[..|s|] == s;
}

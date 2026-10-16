ghost function CountChar(s: seq<char>, c: char): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountChar(s[..|s|-1], c) + (if s[|s|-1] == c then 1 else 0)
}

ghost predicate UsesOnlyFirstKLetters(s: seq<char>, k: int)
{
  forall i | 0 <= i < |s| :: 'a' as int <= s[i] as int < 'a' as int + k
}

ghost predicate EachLetterPresent(s: seq<char>, k: int)
  requires 1 <= k <= 26
{
  forall j | 0 <= j < k :: CountChar(s, ('a' as int + j) as char) >= 1
}

ghost predicate MinFreqIsOptimal(s: seq<char>, n: int, k: int)
  requires 1 <= k <= 26
{
  forall j | 0 <= j < k :: CountChar(s, ('a' as int + j) as char) >= n / k
}

lemma CountCharAppend(s: seq<char>, c: char, d: char)
  ensures CountChar(s + [c], d) == CountChar(s, d) + (if c == d then 1 else 0)
{
  var s' := s + [c];
  assert s'[..|s'| - 1] == s;
}

ghost function ExactCount(i: int, k: int, j: int): int
  requires k >= 1
{
  if j < i % k then i / k + 1 else i / k
}

lemma DivModSucc(i: int, k: int)
  requires k >= 1
  requires i >= 0
  ensures i % k < k - 1 ==> ((i + 1) / k == i / k && (i + 1) % k == i % k + 1)
  ensures i % k == k - 1 ==> ((i + 1) / k == i / k + 1 && (i + 1) % k == 0)
{
  var q := i / k;
  var r := i % k;
  assert i == q * k + r;
  if r < k - 1 {
    assert i + 1 == q * k + (r + 1);
    assert 0 <= r + 1 < k;
    // Uniqueness of Euclidean division: i+1 = q*k + (r+1) with 0 <= r+1 < k
    var dq := (i + 1) / k - q;
    var dr := (i + 1) % k - (r + 1);
    assert dq * k + dr == 0;
    assert -(k - 1) <= dr <= k - 1;
  } else {
    assert r == k - 1;
    assert i + 1 == (q + 1) * k;
    var dq := (i + 1) / k - (q + 1);
    var dr := (i + 1) % k;
    assert dq * k + dr == 0;
    assert 0 <= dr < k;
  }
}

lemma ExactCountStep(i: int, k: int, j: int)
  requires k >= 1
  requires i >= 0
  requires 0 <= j < k
  ensures j == i % k ==> ExactCount(i + 1, k, j) == ExactCount(i, k, j) + 1
  ensures j != i % k ==> ExactCount(i + 1, k, j) == ExactCount(i, k, j)
{
  DivModSucc(i, k);
}

method UniformString(n: int, k: int) returns (s: seq<char>)
  requires 1 <= k <= 26
  requires n >= k
  ensures |s| == n
  ensures UsesOnlyFirstKLetters(s, k)
  ensures EachLetterPresent(s, k)
  ensures MinFreqIsOptimal(s, n, k)
{
  s := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant forall m | 0 <= m < i :: s[m] == ('a' as int + (m % k)) as char
    invariant forall j | 0 <= j < k ::
      CountChar(s, ('a' as int + j) as char) == ExactCount(i, k, j)
    decreases n - i
  {
    var r := i % k;
    var c := ('a' as int + r) as char;
    ghost var old_s := s;
    s := s + [c];

    forall j | 0 <= j < k
      ensures CountChar(s, ('a' as int + j) as char) == ExactCount(i + 1, k, j)
    {
      var d := ('a' as int + j) as char;
      CountCharAppend(old_s, c, d);
      ExactCountStep(i, k, j);
    }

    i := i + 1;
  }

  // Prove UsesOnlyFirstKLetters
  forall m | 0 <= m < |s|
    ensures 'a' as int <= s[m] as int < 'a' as int + k
  {
    assert s[m] == ('a' as int + (m % k)) as char;
    assert 0 <= m % k < k;
  }

  // Prove MinFreqIsOptimal
  forall j | 0 <= j < k
    ensures CountChar(s, ('a' as int + j) as char) >= n / k
  {
    assert CountChar(s, ('a' as int + j) as char) == ExactCount(n, k, j);
    assert ExactCount(n, k, j) >= n / k;
  }

  // Prove EachLetterPresent
  assert n / k >= 1;
  forall j | 0 <= j < k
    ensures CountChar(s, ('a' as int + j) as char) >= 1
  {
    assert CountChar(s, ('a' as int + j) as char) >= n / k;
  }
}

ghost predicate ValidMatrix(M: seq<seq<char>>, n: int)
{
  n >= 0 &&
  |M| == n &&
  (forall i | 0 <= i < n :: |M[i]| == n)
}

ghost predicate IsCrossAt(M: seq<seq<char>>, n: int, a: int, b: int)
  requires ValidMatrix(M, n)
  requires 0 <= a < n && 0 <= b < n
{
  1 <= a <= n - 2 &&
  1 <= b <= n - 2 &&
  M[a][b] == 'X' &&
  M[a-1][b-1] == 'X' &&
  M[a-1][b+1] == 'X' &&
  M[a+1][b-1] == 'X' &&
  M[a+1][b+1] == 'X'
}

ghost function CrossCount(M: seq<seq<char>>, n: int): int
  requires ValidMatrix(M, n)
{
  |set a, b | 0 <= a < n && 0 <= b < n && IsCrossAt(M, n, a, b) :: (a, b)|
}

method CountCrosses(n: int, M: seq<seq<char>>) returns (count: int)
  requires ValidMatrix(M, n)
  ensures count == CrossCount(M, n)
{
  ghost var crossSet := set a, b | 0 <= a < n && 0 <= b < n && IsCrossAt(M, n, a, b) :: (a, b);
  count := 0;
  if n < 3 {
    assert forall a, b | 0 <= a < n && 0 <= b < n :: !IsCrossAt(M, n, a, b);
    assert crossSet == {};
    return;
  }

  ghost var counted: set<(int, int)> := {};

  var a := 1;
  while a < n - 1
    invariant 1 <= a <= n - 1
    invariant counted <= crossSet
    invariant forall i, j :: (i, j) in counted ==> i < a
    invariant forall i, j :: (i, j) in crossSet && i < a ==> (i, j) in counted
    invariant count == |counted|
  {
    var b := 1;
    while b < n - 1
      invariant 1 <= b <= n - 1
      invariant counted <= crossSet
      invariant forall i, j :: (i, j) in counted ==> i < a || (i == a && j < b)
      invariant forall i, j :: (i, j) in crossSet && (i < a || (i == a && j < b)) ==> (i, j) in counted
      invariant count == |counted|
    {
      if M[a][b] == 'X'
         && M[a-1][b-1] == 'X'
         && M[a-1][b+1] == 'X'
         && M[a+1][b-1] == 'X'
         && M[a+1][b+1] == 'X'
      {
        assert IsCrossAt(M, n, a, b);
        assert (a, b) in crossSet;
        assert (a, b) !in counted;
        counted := counted + {(a, b)};
        count := count + 1;
      }
      b := b + 1;
    }
    a := a + 1;
  }

  assert forall i, j :: (i, j) in crossSet ==> i <= n - 2;
  assert forall i, j :: (i, j) in crossSet ==> (i, j) in counted;
  assert counted == crossSet;
}

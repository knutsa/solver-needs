ghost predicate ValidInput(n: int, a: seq<int>, b: seq<int>, c: seq<int>)
{
  n >= 3 &&
  |a| == n && |b| == n && |c| == n &&
  forall i | 0 <= i < n :: a[i] != b[i] && a[i] != c[i] && b[i] != c[i]
}

ghost predicate ChosenFromOptions(p: seq<int>, a: seq<int>, b: seq<int>, c: seq<int>)
  requires |p| == |a| == |b| == |c|
{
  forall i | 0 <= i < |p| :: p[i] == a[i] || p[i] == b[i] || p[i] == c[i]
}

ghost predicate NoAdjacentEqual(p: seq<int>)
  requires |p| >= 1
{
  // Consecutive pairs
  (forall i | 0 <= i < |p| - 1 :: p[i] != p[i + 1]) &&
  // Circular wrap-around: last element != first element
  p[|p| - 1] != p[0]
}

ghost predicate ValidColoring(p: seq<int>, n: int, a: seq<int>, b: seq<int>, c: seq<int>)
{
  |p| == n && n >= 3 &&
  |a| == n && |b| == n && |c| == n &&
  ChosenFromOptions(p, a, b, c) &&
  NoAdjacentEqual(p)
}

method CircleColoring(n: int, a: seq<int>, b: seq<int>, c: seq<int>) returns (p: seq<int>)
  requires ValidInput(n, a, b, c)
  ensures ValidColoring(p, n, a, b, c)
{
  var out := new int[n];
  out[0] := a[0];

  // Elements 1..n-2: pick one that differs from previous
  var i := 1;
  while i < n - 1
    invariant 1 <= i <= n - 1
    invariant forall j | 0 <= j < i :: out[j] == a[j] || out[j] == b[j] || out[j] == c[j]
    invariant forall j | 1 <= j < i :: out[j] != out[j - 1]
  {
    if a[i] != out[i - 1] {
      out[i] := a[i];
    } else {
      // a[i] == out[i-1] and a[i] != b[i], so b[i] != out[i-1]
      out[i] := b[i];
    }
    i := i + 1;
  }

  // Last element: must differ from both out[n-2] and out[0]
  // We have 3 pairwise-distinct choices and at most 2 forbidden values,
  // so at least one choice works.
  if a[n - 1] != out[n - 2] && a[n - 1] != out[0] {
    out[n - 1] := a[n - 1];
  } else if b[n - 1] != out[n - 2] && b[n - 1] != out[0] {
    out[n - 1] := b[n - 1];
  } else {
    // Both a and b are blocked. Prove c works:
    // a[n-1] ∈ {out[n-2], out[0]} and b[n-1] ∈ {out[n-2], out[0]}
    // Since a[n-1] != b[n-1], they cover both forbidden values.
    // Since c[n-1] != a[n-1] and c[n-1] != b[n-1], c avoids both.
    assert a[n - 1] == out[n - 2] || a[n - 1] == out[0];
    assert b[n - 1] == out[n - 2] || b[n - 1] == out[0];
    out[n - 1] := c[n - 1];
  }

  p := out[..];
}

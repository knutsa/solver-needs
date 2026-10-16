ghost predicate CanFormTriangle(x: int, y: int, z: int)
{
  x + y > z && x + z > y && y + z > x
}

ghost predicate Sorted(a: seq<int>)
{
  forall i, j | 0 <= i && i <= j && j < |a| :: a[i] <= a[j]
}

lemma AllTrianglesValid(a: seq<int>)
  requires |a| >= 3
  requires Sorted(a)
  requires a[0] + a[1] > a[|a| - 1]
  ensures forall i, j, k | 0 <= i && i < j && j < k && k < |a| ::
    CanFormTriangle(a[i], a[j], a[k])
{
  var n := |a|;
  forall i, j, k | 0 <= i && i < j && j < k && k < n
    ensures CanFormTriangle(a[i], a[j], a[k])
  {
    // From Sorted and a[0]+a[1] > a[n-1]:
    // a[n-1] >= a[1] >= a[0], so a[0]+a[1] > a[n-1] >= a[1] => a[0] > 0
    // and a[0]+a[1] > a[n-1] >= a[0] => a[1] > 0
    assert a[0] > 0;
    assert a[1] > 0;

    // i >= 0, j >= 1, k >= 2 from i < j < k
    assert a[i] >= a[0];
    assert a[j] >= a[1];
    assert a[k] <= a[n - 1];

    // Cond 1: a[i]+a[j] >= a[0]+a[1] > a[n-1] >= a[k]
    assert a[i] + a[j] > a[k];

    // Cond 2: a[k] >= a[j] and a[i] >= a[0] > 0 => a[i]+a[k] > a[j]
    assert a[k] >= a[j];
    assert a[i] + a[k] > a[j];

    // Cond 3: a[j] >= a[i] and a[k] >= a[1] > 0 => a[j]+a[k] > a[i]
    assert a[j] >= a[i];
    assert a[j] + a[k] > a[i];
  }
}

method BadTriangle(a: seq<int>) returns (result: (int, int, int), found: bool)
  requires |a| >= 3
  requires Sorted(a)
  ensures found ==>
    1 <= result.0 && result.0 < result.1 && result.1 < result.2 && result.2 <= |a| &&
    !CanFormTriangle(a[result.0 - 1], a[result.1 - 1], a[result.2 - 1])
  ensures !found ==>
    forall i, j, k | 0 <= i && i < j && j < k && k < |a| ::
      CanFormTriangle(a[i], a[j], a[k])
{
  result := (0, 0, 0);
  found := false;
  var n := |a|;

  var x := a[0] + a[1] - a[n - 1];
  var y := a[0] - a[1] + a[n - 1];
  var z := -a[0] + a[1] + a[n - 1];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, 2, n);
    found := true;
    return;
  }

  x := a[0] + a[n - 1] - a[n - 2];
  y := a[0] - a[n - 1] + a[n - 2];
  z := -a[0] + a[n - 1] + a[n - 2];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, n - 1, n);
    found := true;
    return;
  }

  x := a[0] + a[1] - a[2];
  y := a[0] - a[1] + a[2];
  z := -a[0] + a[1] + a[2];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (1, 2, 3);
    found := true;
    return;
  }

  x := a[n - 3] + a[n - 2] - a[n - 1];
  y := a[n - 3] - a[n - 2] + a[n - 1];
  z := -a[n - 3] + a[n - 2] + a[n - 1];
  if x <= 0 || y <= 0 || z <= 0 {
    result := (n - 2, n - 1, n);
    found := true;
    return;
  }

  // All checks passed => a[0] + a[1] > a[n-1]
  AllTrianglesValid(a);
}

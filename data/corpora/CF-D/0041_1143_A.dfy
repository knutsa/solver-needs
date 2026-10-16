// Count occurrences of value v in sequence s
ghost function CountVal(s: seq<int>, v: int): int
  decreases |s|
{
  if |s| == 0 then 0
  else CountVal(s[..|s|-1], v) + (if s[|s|-1] == v then 1 else 0)
}

// After opening the first k doors in order, Mr. Black can exit iff
// all doors belonging to at least one exit are open. A door belongs
// to exit 0 (left) or exit 1 (right). All doors of exit e are open
// when the count of e in doors[..k] equals the total count of e in doors.
ghost predicate CanExitAfter(doors: seq<int>, k: int)
  requires 0 <= k <= |doors|
{
  CountVal(doors[..k], 0) == CountVal(doors, 0) ||
  CountVal(doors[..k], 1) == CountVal(doors, 1)
}

method TheDoors(n: int, doors: seq<int>) returns (k: int)
  requires n == |doors|
  requires n >= 2
  requires forall i | 0 <= i < n :: doors[i] == 0 || doors[i] == 1
  requires CountVal(doors, 0) >= 1
  requires CountVal(doors, 1) >= 1
  ensures 1 <= k <= n
  ensures CanExitAfter(doors, k)
  ensures forall j | 0 <= j < k :: !CanExitAfter(doors, j)
{
  var a := 0;
  var b := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant a == CountVal(doors[..i], 0)
    invariant b == CountVal(doors[..i], 1)
  {
    // assert doors[i] == 0 || doors[i] == 1;
    assert doors[..i+1][..i] == doors[..i];
    if doors[i] == 0 {
      a := a + 1;
    } else {
      b := b + 1;
    }
    i := i + 1;
  }
  assert doors[..n] == doors;

  var x := 0;
  var y := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant x == CountVal(doors[..i], 0)
    invariant y == CountVal(doors[..i], 1)
    invariant forall j | 0 <= j <= i :: !CanExitAfter(doors, j)
  {
    // assert doors[i] == 0 || doors[i] == 1;
    assert doors[..i+1][..i] == doors[..i];
    if doors[i] == 1 {
      y := y + 1;
    } else {
      x := x + 1;
    }
    if x == a || y == b {
      return i + 1;
    }
    // assert !CanExitAfter(doors, i + 1);
    i := i + 1;
  }
  assert doors[..n] == doors;
  assert CanExitAfter(doors, n);
  return 0;
}

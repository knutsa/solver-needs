// === Formal Specification ===

// The number of adjacent-floor transitions between two floors.
// Two floors are adjacent if their numbers differ by one.
ghost function FloorDistance(a: int, b: int): int
{
  if a >= b then a - b else b - a
}

// Time for Masha to walk from floor x to floor y using the stairs.
// Each adjacent-floor transition takes t1 seconds.
ghost function StairsTime(x: int, y: int, t1: int): int
{
  t1 * FloorDistance(x, y)
}

// Time for the elevator to travel from its current floor z to Masha's floor x.
// Each adjacent-floor transition takes t2 seconds.
ghost function ElevatorApproachTime(z: int, x: int, t2: int): int
{
  t2 * FloorDistance(z, x)
}

// Time for the elevator to carry Masha from floor x to Egor's floor y.
// Each adjacent-floor transition takes t2 seconds.
ghost function ElevatorRideTime(x: int, y: int, t2: int): int
{
  t2 * FloorDistance(x, y)
}

// Time for door operations during elevator use.
// Three operations: open at Masha's floor, close at Masha's floor, open at Egor's floor.
// Each operation takes t3 seconds.
ghost function DoorOpsTime(t3: int): int
{
  3 * t3
}

// Total time when using the elevator: approach + ride + door operations.
ghost function ElevatorTotalTime(x: int, y: int, z: int, t2: int, t3: int): int
{
  ElevatorApproachTime(z, x, t2) + ElevatorRideTime(x, y, t2) + DoorOpsTime(t3)
}

// Masha uses the elevator unless the stairs time is strictly less than the elevator time.
ghost predicate ShouldUseElevator(x: int, y: int, z: int, t1: int, t2: int, t3: int)
{
  StairsTime(x, y, t1) >= ElevatorTotalTime(x, y, z, t2, t3)
}

// === Method with specification ===

method ElevatorOrStairs(x: int, y: int, z: int, t1: int, t2: int, t3: int) returns (result: string)
  requires x >= 1 && y >= 1 && z >= 1
  requires x != y
  requires t1 >= 1 && t2 >= 1 && t3 >= 1
  ensures result == "YES" <==> ShouldUseElevator(x, y, z, t1, t2, t3)
  ensures result == "YES" || result == "NO"
{
  var dxy := if x >= y then x - y else y - x;
  var dxz := if x >= z then x - z else z - x;

  assert dxy == FloorDistance(x, y);
  assert dxz == FloorDistance(z, x);
  assert t1 * dxy == StairsTime(x, y, t1);
  assert t2 * dxz == ElevatorApproachTime(z, x, t2);
  assert t2 * dxy == ElevatorRideTime(x, y, t2);
  assert t3 * 3 == DoorOpsTime(t3);
  assert t2 * dxy + t2 * dxz + t3 * 3 == ElevatorTotalTime(x, y, z, t2, t3);

  if t1 * dxy >= t2 * dxy + t2 * dxz + t3 * 3 {
    result := "YES";
  } else {
    result := "NO";
  }
}

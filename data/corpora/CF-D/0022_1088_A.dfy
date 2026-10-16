ghost predicate ValidPair(a: int, b: int, x: int)
{
  1 <= a <= x &&
  1 <= b <= x &&
  a % b == 0 &&
  a * b > x &&
  a / b < x
}

ghost predicate SolutionExists(x: int)
{
  exists a :: exists b :: ValidPair(a, b, x)
}

method EhabConstruction(x: int) returns (a: int, b: int, found: bool)
  ensures found ==> ValidPair(a, b, x)
  ensures !found ==> !SolutionExists(x)
{
  a := 0;
  b := 0;
  found := false;

  var ai := 1;
  while ai <= x && !found
    invariant 1 <= ai
    invariant found ==> ValidPair(a, b, x)
    invariant !found ==> forall a', b' :: 1 <= a' < ai && 1 <= b' <= x ==> !ValidPair(a', b', x)
  {
    var bi := 1;
    while bi <= ai && !found
      invariant 1 <= bi
      invariant found ==> ValidPair(a, b, x)
      invariant !found ==> forall a', b' :: 1 <= a' < ai && 1 <= b' <= x ==> !ValidPair(a', b', x)
      invariant !found ==> forall b' :: 1 <= b' < bi ==> !ValidPair(ai, b', x)
    {
      if ai % bi == 0 && ai * bi > x && ai / bi < x {
        a := ai;
        b := bi;
        found := true;
      }
      bi := bi + 1;
    }
    if !found {
      // For b' > ai: since 1 <= ai < b', ai % b' == ai >= 1 != 0, so ValidPair is false
      assert forall b' :: ai < b' <= x ==> !ValidPair(ai, b', x) by {
        forall b' | ai < b' <= x
          ensures !ValidPair(ai, b', x)
        {
          assert ai % b' == ai;
        }
      }
    }
    ai := ai + 1;
  }
}

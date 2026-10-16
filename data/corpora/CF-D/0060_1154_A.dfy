ghost function RemoveIndex(s: seq<int>, m: int): seq<int>
  requires 0 <= m < |s|
  ensures |RemoveIndex(s, m)| == |s| - 1
{
  s[..m] + s[m+1..]
}

// Core postcondition: a, b, c are positive and their pairwise sums
// plus total sum form exactly the input (in any order).
ghost predicate IsValidRestoration(x: seq<int>, a: int, b: int, c: int)
{
  |x| == 4 &&
  a > 0 && b > 0 && c > 0 &&
  multiset{a + b, a + c, b + c, a + b + c} == multiset(x)
}

// Compilable precondition: the input admits some valid (a, b, c).
// Since a+b+c > any pairwise sum when a,b,c > 0, the total must be
// one of the four elements — so we enumerate the 4 candidates.
ghost predicate HasValidRestoration(x: seq<int>)
  requires |x| == 4
{
  exists m | 0 <= m < 4 ::
    var rest := RemoveIndex(x, m);
    var a := x[m] - rest[0];
    var b := x[m] - rest[1];
    var c := x[m] - rest[2];
    a > 0 && b > 0 && c > 0 &&
    multiset{a + b, a + c, b + c, a + b + c} == multiset(x)
}

ghost predicate CheckIndex(x: seq<int>, m: int)
  requires |x| == 4
  requires 0 <= m < 4
{
  var rest := RemoveIndex(x, m);
  var a := x[m] - rest[0];
  var b := x[m] - rest[1];
  var c := x[m] - rest[2];
  a > 0 && b > 0 && c > 0 &&
  multiset{a + b, a + c, b + c, a + b + c} == multiset(x)
}

lemma HasValidMeansOneWorks(x: seq<int>)
  requires |x| == 4
  requires HasValidRestoration(x)
  ensures CheckIndex(x, 0) || CheckIndex(x, 1) || CheckIndex(x, 2) || CheckIndex(x, 3)
{
}

method RestoreThreeNumbers(x: seq<int>) returns (a: int, b: int, c: int)
  requires |x| == 4
  requires HasValidRestoration(x)
  ensures IsValidRestoration(x, a, b, c)
{
  HasValidMeansOneWorks(x);

  assert RemoveIndex(x, 0) == [x[1], x[2], x[3]];
  assert RemoveIndex(x, 1) == [x[0], x[2], x[3]];
  assert RemoveIndex(x, 2) == [x[0], x[1], x[3]];
  assert RemoveIndex(x, 3) == [x[0], x[1], x[2]];

  // Try m=0
  a := x[0] - x[1]; b := x[0] - x[2]; c := x[0] - x[3];
  if a > 0 && b > 0 && c > 0 && multiset{a+b, a+c, b+c, a+b+c} == multiset(x) {
    return;
  }

  // Try m=1
  a := x[1] - x[0]; b := x[1] - x[2]; c := x[1] - x[3];
  if a > 0 && b > 0 && c > 0 && multiset{a+b, a+c, b+c, a+b+c} == multiset(x) {
    return;
  }

  // Try m=2
  a := x[2] - x[0]; b := x[2] - x[1]; c := x[2] - x[3];
  if a > 0 && b > 0 && c > 0 && multiset{a+b, a+c, b+c, a+b+c} == multiset(x) {
    return;
  }

  // m=3 must work
  a := x[3] - x[0]; b := x[3] - x[1]; c := x[3] - x[2];
}

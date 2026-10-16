// The frog's position after k jumps, defined directly from the problem statement:
//   Start at position 0. Before each jump, count prior jumps:
//     even count  → jump right by a  (position += a)
//     odd  count  → jump left  by b  (position -= b)
ghost function FrogPosition(a: int, b: int, k: nat): real
  decreases k
{
  if k == 0 then 0.0
  else if (k - 1) % 2 == 0 then
    FrogPosition(a, b, k - 1) + a as real
  else
    FrogPosition(a, b, k - 1) - b as real
}

lemma FrogPositionClosedForm(a: int, b: int, k: nat)
  ensures FrogPosition(a, b, k) ==
    (k / 2) as real * a as real - (k / 2) as real * b as real + (if k % 2 == 1 then a as real else 0.0)
  decreases k
{
  if k == 0 {
  } else if k == 1 {
  } else {
    FrogPositionClosedForm(a, b, k - 1);
    if (k - 1) % 2 == 0 {
      // k is odd, k-1 is even
      assert (k - 1) / 2 == k / 2;
    } else {
      // k is even, k-1 is odd
      assert (k - 1) / 2 + 1 == k / 2;
    }
  }
}

method FrogJumping(queries: seq<(int, int, int)>) returns (results: seq<real>)
  requires forall i | 0 <= i < |queries| :: queries[i].2 >= 0
  ensures |results| == |queries|
  ensures forall i | 0 <= i < |queries| ::
    results[i] == FrogPosition(queries[i].0, queries[i].1, queries[i].2)
{
  results := [];
  var i := 0;
  while i < |queries|
    invariant 0 <= i <= |queries|
    invariant |results| == i
    invariant forall j | 0 <= j < i :: results[j] == FrogPosition(queries[j].0, queries[j].1, queries[j].2)
  {
    var (a, b, k) := queries[i];
    var half := k / 2;
    var ans: real := a as real * half as real - b as real * half as real;
    if k % 2 == 1 {
      ans := ans + a as real;
    }
    FrogPositionClosedForm(a, b, k);
    results := results + [ans];
    i := i + 1;
  }
}

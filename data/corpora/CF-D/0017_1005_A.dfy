// Generates the counting sequence [1, 2, ..., n]
ghost function CountingSeq(n: int): seq<int>
  decreases n
{
  if n <= 0 then [] else CountingSeq(n - 1) + [n]
}

// Every element is at least 1 (each stairway has at least one step)
ghost predicate AllPositive(s: seq<int>)
{
  forall i | 0 <= i < |s| :: s[i] >= 1
}

// Concatenates counting sequences: [1..stairs[0]] ++ [1..stairs[1]] ++ ...
ghost function ConcatStairways(stairs: seq<int>): seq<int>
  decreases |stairs|
{
  if |stairs| == 0 then []
  else ConcatStairways(stairs[..|stairs|-1]) + CountingSeq(stairs[|stairs|-1])
}

// The input is a valid pronunciation: starts at 1, each next element
// either starts a new stairway (== 1) or continues the count (== prev + 1)
ghost predicate IsValidInput(a: seq<int>)
{
  |a| >= 1 &&
  a[0] == 1 &&
  forall i | 1 <= i < |a| :: a[i] == 1 || a[i] == a[i - 1] + 1
}

method TanyaAndStairways(a: seq<int>) returns (t: int, stairs: seq<int>)
  requires IsValidInput(a)
  ensures t == |stairs|
  ensures t >= 1
  ensures AllPositive(stairs)
  ensures ConcatStairways(stairs) == a
{
  stairs := [];
  var cnt := 0;
  for i := 0 to |a|
    invariant i == 0 ==> cnt == 0 && stairs == []
    invariant i > 0 ==> cnt == a[i-1] && cnt >= 1
    invariant AllPositive(stairs)
    invariant ConcatStairways(stairs) + CountingSeq(cnt) == a[..i]
  {
    if i == 0 {
      cnt := 1;
    } else if a[i] == 1 {
      assert ConcatStairways(stairs + [cnt]) == ConcatStairways(stairs) + CountingSeq(cnt);
      stairs := stairs + [cnt];
      cnt := 1;
    } else {
      cnt := cnt + 1;
    }
  }
  assert a[..|a|] == a;
  stairs := stairs + [cnt];
  t := |stairs|;
}

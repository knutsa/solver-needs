ghost predicate AllConsiderEasy(opinions: seq<int>)
{
  forall i | 0 <= i < |opinions| :: opinions[i] == 0
}

method IsEasyProblem(n: int, opinions: seq<int>) returns (result: string)
  ensures AllConsiderEasy(opinions) ==> result == "EASY"
  ensures !AllConsiderEasy(opinions) ==> result == "HARD"
{
  var allZero := true;
  var i := 0;
  while i < |opinions|
    invariant 0 <= i <= |opinions|
    invariant allZero <==> AllConsiderEasy(opinions[..i])
  {
    if opinions[i] != 0 {
      allZero := false;
    }
    i := i + 1;
  }
  assert opinions[..|opinions|] == opinions;
  if allZero {
    result := "EASY";
  } else {
    result := "HARD";
  }
}

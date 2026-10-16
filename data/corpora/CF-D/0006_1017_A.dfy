// The total score for a student (sum of their 4 subject scores).
ghost function TotalScore(student: seq<int>): int
  requires |student| >= 4
{
  student[0] + student[1] + student[2] + student[3]
}

// Count how many students in the given sequence have a total score
// strictly greater than the threshold.
ghost function CountBetter(students: seq<seq<int>>, threshold: int): int
  requires forall i | 0 <= i < |students| :: |students[i]| >= 4
  decreases |students|
{
  if |students| == 0 then 0
  else
    CountBetter(students[..|students|-1], threshold)
    + (if TotalScore(students[|students|-1]) > threshold then 1 else 0)
}

// A student "ranks above" Thomas if their total score is strictly higher,
// or their total score is equal and their id is smaller. Since Thomas has
// id 1 (index 0), no other student (index >= 1) has a smaller id.
// Therefore, a student ranks above Thomas iff their score is strictly higher.
//
// The rank of Thomas is 1 + the number of students who rank above him.
// Per the problem: students are sorted by decreasing total score, with ties
// broken by increasing id. Thomas (id 1) has the smallest id, so among
// students with equal sums, Thomas always comes first.
ghost function ExpectedRank(n: int, scores: seq<seq<int>>): int
  requires n >= 1
  requires |scores| >= n
  requires forall i | 0 <= i < n :: |scores[i]| >= 4
{
  // Count students at indices 1..n-1 who scored strictly higher than Thomas,
  // then add 1.
  1 + CountBetter(scores[1..n], TotalScore(scores[0]))
}


method TheRank(n: int, scores: seq<seq<int>>) returns (rank: int)
  requires n >= 1
  requires |scores| >= n
  requires forall i | 0 <= i < n :: |scores[i]| >= 4
  ensures rank == ExpectedRank(n, scores)
{
  var myScore := scores[0][0] + scores[0][1] + scores[0][2] + scores[0][3];
  rank := 1;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant rank == 1 + CountBetter(scores[1..i], myScore)
  {
    var otherScore := scores[i][0] + scores[i][1] + scores[i][2] + scores[i][3];

    // Key assertion: scores[1..i+1] == scores[1..i] + [scores[i]]
    assert scores[1..i+1] == scores[1..i] + [scores[i]];
    // Inlined from CountBetterAppend(scores[1..i], myScore, scores[i])
    var combined := (scores[1..i]) + [(scores[i])];
    assert combined[..|combined|-1] == (scores[1..i]);
    assert CountBetter(scores[1..i] + [scores[i]], myScore) == CountBetter(scores[1..i], myScore) + (if TotalScore(scores[i]) > myScore then 1 else 0);

    if otherScore > myScore {
      rank := rank + 1;
    }
    i := i + 1;
  }
  assert scores[1..n] == scores[1..i];
  return;
}

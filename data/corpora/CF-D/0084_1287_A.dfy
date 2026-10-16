ghost predicate ValidState(s: seq<char>)
{
  forall i | 0 <= i < |s| :: s[i] == 'A' || s[i] == 'P'
}

// One simultaneous round: every angry student makes the next student angry
ghost function OneStep(s: seq<char>): seq<char>
{
  seq(|s|, j requires 0 <= j < |s| =>
    if s[j] == 'A' || (j > 0 && s[j-1] == 'A' && s[j] == 'P') then 'A' else s[j])
}

// Apply the snowball-throwing rule `steps` times
ghost function Simulate(s: seq<char>, steps: nat): seq<char>
  decreases steps
{
  if steps == 0 then s else Simulate(OneStep(s), steps - 1)
}

// No student becomes angry in the next round
ghost predicate IsFixedPoint(s: seq<char>)
{
  OneStep(s) == s
}

lemma OneStepPreservesValid(s: seq<char>)
  requires ValidState(s)
  ensures ValidState(OneStep(s))
{
  forall i | 0 <= i < |OneStep(s)|
    ensures OneStep(s)[i] == 'A' || OneStep(s)[i] == 'P'
  {
  }
}

lemma SimulateStep(s: seq<char>, n: nat)
  ensures OneStep(Simulate(s, n)) == Simulate(s, n + 1)
  decreases n
{
  if n > 0 {
    SimulateStep(OneStep(s), n - 1);
  }
}

method AngryStudents(s: string) returns (steps: int)
  decreases *
  requires ValidState(s)
  ensures steps >= 0
  ensures IsFixedPoint(Simulate(s, steps))
  ensures forall k: int | 0 <= k < steps :: !IsFixedPoint(Simulate(s, k))
{
  var n := |s|;
  var line := new char[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k | 0 <= k < i :: line[k] == s[k]
  {
    line[i] := s[i];
    i := i + 1;
  }
  assert line[..] == s;

  steps := 0;
  while true
    decreases *
    invariant steps >= 0
    invariant line[..] == Simulate(s, steps)
    invariant ValidState(line[..])
    invariant forall k: int | 0 <= k < steps :: !IsFixedPoint(Simulate(s, k))
  {
    ghost var oldSeq := line[..];
    var flag := false;
    var j := n - 1;
    ghost var changeIdx := -1;

    while j >= 0
      invariant -1 <= j <= n - 1
      invariant line.Length == n
      invariant |oldSeq| == n
      invariant ValidState(oldSeq)
      invariant oldSeq == Simulate(s, steps)
      // Prefix: positions 0..j+1 unchanged
      invariant forall k | 0 <= k <= j + 1 && k < n :: line[k] == oldSeq[k]
      // Suffix: positions j+2..n-1 match OneStep
      invariant forall k | j + 2 <= k < n :: line[k] == OneStep(oldSeq)[k]
      // Flag: tracks whether any change was made
      invariant flag ==> (0 <= changeIdx < n && OneStep(oldSeq)[changeIdx] != oldSeq[changeIdx])
      invariant !flag ==> (forall k | j + 2 <= k < n :: OneStep(oldSeq)[k] == oldSeq[k])
    {
      if line[j] == 'A' && j + 1 < n && line[j + 1] == 'P' {
        assert line[j] == oldSeq[j];
        assert line[j + 1] == oldSeq[j + 1];
        assert oldSeq[j] == 'A' && oldSeq[j + 1] == 'P';
        assert j + 1 > 0;
        assert OneStep(oldSeq)[j + 1] == 'A';
        assert OneStep(oldSeq)[j + 1] != oldSeq[j + 1];
        line[j + 1] := 'A';
        flag := true;
        changeIdx := j + 1;
      } else if j + 1 < n {
        assert line[j] == oldSeq[j];
        assert line[j + 1] == oldSeq[j + 1];
        assert !(oldSeq[j] == 'A' && oldSeq[j + 1] == 'P');
        assert OneStep(oldSeq)[j + 1] == oldSeq[j + 1];
      }
      j := j - 1;
    }

    // After inner loop: j == -1
    // Position 0 is unchanged by OneStep (no predecessor)
    if n > 0 {
      assert OneStep(oldSeq)[0] == oldSeq[0];
      assert line[0] == oldSeq[0];
    }
    assert forall k | 0 <= k < n :: line[k] == OneStep(oldSeq)[k];
    assert line[..] == OneStep(oldSeq);

    if !flag {
      // No changes: OneStep(oldSeq) == oldSeq
      assert forall k | 0 <= k < n :: OneStep(oldSeq)[k] == oldSeq[k];
      assert OneStep(oldSeq) == oldSeq;
      assert IsFixedPoint(Simulate(s, steps));
      break;
    }

    // Changes were made: not a fixed point
    assert OneStep(oldSeq) != oldSeq;
    assert !IsFixedPoint(Simulate(s, steps));
    SimulateStep(s, steps);
    OneStepPreservesValid(oldSeq);
    steps := steps + 1;
  }
}

method {:verify false} Main()
  decreases *
{
  var r: int;

  // Test 1
  r := AngryStudents("PPAP");
  expect r == 1, "PPAP";

  // Test 2
  r := AngryStudents("APPAPPPAPPPP");
  expect r == 4, "APPAPPPAPPPP";
  r := AngryStudents("AAP");
  expect r == 1, "AAP";
  r := AngryStudents("PPA");
  expect r == 0, "PPA";

  // Test 3
  r := AngryStudents("A");
  expect r == 0, "A";
  r := AngryStudents("P");
  expect r == 0, "P";
  r := AngryStudents("AP");
  expect r == 1, "AP";
  r := AngryStudents("PA");
  expect r == 0, "PA";
  r := AngryStudents("PPPPAPPP");
  expect r == 3, "PPPPAPPP";
  r := AngryStudents("PPPPPPPA");
  expect r == 0, "PPPPPPPA";
  r := AngryStudents("APPPPPPP");
  expect r == 7, "APPPPPPP";
  r := AngryStudents("PPPPPPAP");
  expect r == 1, "PPPPPPAP";
  r := AngryStudents("PPPPPAPP");
  expect r == 2, "PPPPPAPP";
  r := AngryStudents("PPPAPPPP");
  expect r == 4, "PPPAPPPP";

  // Test 4
  r := AngryStudents("PPPP");
  expect r == 0, "PPPP";
  r := AngryStudents("APPP");
  expect r == 3, "APPP";
  r := AngryStudents("PAPP");
  expect r == 2, "PAPP";
  r := AngryStudents("AAPP");
  expect r == 2, "AAPP";
  r := AngryStudents("PPAP");
  expect r == 1, "PPAP 2";
  r := AngryStudents("APAP");
  expect r == 1, "APAP";
  r := AngryStudents("PAAP");
  expect r == 1, "PAAP";
  r := AngryStudents("AAAP");
  expect r == 1, "AAAP";
  r := AngryStudents("PPPA");
  expect r == 0, "PPPA";
  r := AngryStudents("APPA");
  expect r == 2, "APPA";
  r := AngryStudents("PAPA");
  expect r == 1, "PAPA";
  r := AngryStudents("AAPA");
  expect r == 1, "AAPA";
  r := AngryStudents("PPAA");
  expect r == 0, "PPAA";
  r := AngryStudents("APAA");
  expect r == 1, "APAA";
  r := AngryStudents("PAAA");
  expect r == 0, "PAAA";
  r := AngryStudents("AAAA");
  expect r == 0, "AAAA";

  // Test 5
  r := AngryStudents("PAPPPAPAAPAAPAAPPAAAPPAPPAPAAAAPPAPPAPPPAAAAAAPPAAAPAAAAAPAPAPAAAAPPAPAAAAPPAPPPPPAAAAAAAPAAAAPAPPAP");
  expect r == 5, "long string";

  print "All tests passed\n";
}

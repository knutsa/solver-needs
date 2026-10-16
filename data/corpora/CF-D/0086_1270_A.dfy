// ── Spec helpers (unchanged) ──────────────────────────────────────────

ghost function SeqToSet(s: seq<int>): set<int>
  decreases |s|
{
  if |s| == 0 then {} else {s[|s|-1]} + SeqToSet(s[..|s|-1])
}

ghost predicate NoDuplicates(s: seq<int>)
{
  forall i, j | 0 <= i < j < |s| :: s[i] != s[j]
}

ghost predicate ValidDeck(n: int, a: seq<int>, b: seq<int>)
{
  n >= 2
  && |a| >= 1
  && |b| >= 1
  && NoDuplicates(a)
  && NoDuplicates(b)
  && SeqToSet(a) !! SeqToSet(b)
  && SeqToSet(a) + SeqToSet(b) == set i | 1 <= i <= n :: i
}

ghost predicate Player1CanWin(S1: set<int>, S2: set<int>, steps: nat)
  decreases steps
{
  if S2 == {} then true
  else if S1 == {} || steps == 0 then false
  else exists c1 | c1 in S1 :: forall c2 | c2 in S2 ::
    if c1 > c2 then Player1CanWin(S1 + {c2}, S2 - {c2}, steps - 1)
    else Player1CanWin(S1 - {c1}, S2 + {c1}, steps - 1)
}

ghost predicate Player1WinsGame(S1: set<int>, S2: set<int>, bound: nat)
{
  exists steps: nat :: Player1CanWin(S1, S2, steps)
}

// ── Helper lemmas ─────────────────────────────────────────────────────

lemma SeqToSetMembership(s: seq<int>, x: int)
  ensures x in SeqToSet(s) <==> exists k | 0 <= k < |s| :: s[k] == x
  decreases |s|
{
  if |s| == 0 {
  } else {
    SeqToSetMembership(s[..|s|-1], x);
    forall k | 0 <= k < |s| - 1
      ensures s[..|s|-1][k] == s[k]
    {}
  }
}

// If Player 1 has a card m that beats every card in S2, Player 1 wins in |S2| steps.
lemma Player1WinsWithMax(S1: set<int>, S2: set<int>, m: int)
  requires m in S1
  requires forall x | x in S2 :: x < m
  decreases |S2|
  ensures Player1CanWin(S1, S2, |S2|)
{
  if S2 == {} {
  } else {
    forall c2 | c2 in S2
      ensures Player1CanWin(S1 + {c2}, S2 - {c2}, |S2| - 1)
    {
      assert |S2 - {c2}| == |S2| - 1;
      Player1WinsWithMax(S1 + {c2}, S2 - {c2}, m);
    }
    assert m in S1;
    assert forall c2 | c2 in S2 :: m > c2;
    assert forall c2 | c2 in S2 ::
      (if m > c2 then Player1CanWin(S1 + {c2}, S2 - {c2}, |S2| - 1)
       else Player1CanWin(S1 - {m}, S2 + {m}, |S2| - 1));
  }
}

// If Player 2 has a card m that beats every card in S1, Player 1 cannot win.
lemma Player1LosesWithoutMax(S1: set<int>, S2: set<int>, m: int, steps: nat)
  requires m in S2
  requires forall x | x in S1 :: x < m
  decreases steps
  ensures !Player1CanWin(S1, S2, steps)
{
  if S1 == {} || steps == 0 {
  } else {
    // Proof by contradiction
    if Player1CanWin(S1, S2, steps) {
      assert S2 != {};
      var c1 :| c1 in S1 && (forall c2 | c2 in S2 ::
        if c1 > c2 then Player1CanWin(S1 + {c2}, S2 - {c2}, steps - 1)
        else Player1CanWin(S1 - {c1}, S2 + {c1}, steps - 1));
      assert c1 < m;
      // Instantiate universal with c2 = m: since c1 < m, else branch taken
      assert Player1CanWin(S1 - {c1}, S2 + {c1}, steps - 1);
      // But by induction hypothesis this is false
      Player1LosesWithoutMax(S1 - {c1}, S2 + {c1}, m, steps - 1);
      assert false;
    }
  }
}

// ── Method ────────────────────────────────────────────────────────────

method CardGame(n: int, k1: int, k2: int, a: seq<int>, b: seq<int>) returns (firstPlayerWins: bool)
  requires ValidDeck(n, a, b)
  requires k1 == |a| && k2 == |b|
  ensures firstPlayerWins <==> Player1WinsGame(SeqToSet(a), SeqToSet(b), n)
{
  var maxA := a[0];
  var i := 1;
  while i < |a|
    invariant 1 <= i <= |a|
    invariant forall k | 0 <= k < i :: a[k] <= maxA
    invariant exists k | 0 <= k < i :: a[k] == maxA
  {
    if a[i] > maxA {
      maxA := a[i];
    }
    i := i + 1;
  }

  var maxB := b[0];
  var j := 1;
  while j < |b|
    invariant 1 <= j <= |b|
    invariant forall k | 0 <= k < j :: b[k] <= maxB
    invariant exists k | 0 <= k < j :: b[k] == maxB
  {
    if b[j] > maxB {
      maxB := b[j];
    }
    j := j + 1;
  }

  firstPlayerWins := maxA > maxB;

  // Prove maxA is in SeqToSet(a) and is its maximum
  ghost var ka :| 0 <= ka < |a| && a[ka] == maxA;
  SeqToSetMembership(a, maxA);
  assert maxA in SeqToSet(a);

  ghost var kb :| 0 <= kb < |b| && b[kb] == maxB;
  SeqToSetMembership(b, maxB);
  assert maxB in SeqToSet(b);

  forall x | x in SeqToSet(a)
    ensures x <= maxA
  {
    SeqToSetMembership(a, x);
    var kx :| 0 <= kx < |a| && a[kx] == x;
  }

  forall x | x in SeqToSet(b)
    ensures x <= maxB
  {
    SeqToSetMembership(b, x);
    var kx :| 0 <= kx < |b| && b[kx] == x;
  }

  // maxA != maxB because they're in disjoint sets
  assert maxA != maxB;

  if maxA > maxB {
    assert forall x | x in SeqToSet(b) :: x < maxA;
    Player1WinsWithMax(SeqToSet(a), SeqToSet(b), maxA);
    assert Player1CanWin(SeqToSet(a), SeqToSet(b), |SeqToSet(b)|);
  } else {
    assert maxB > maxA;
    assert forall x | x in SeqToSet(a) :: x < maxB;
    forall steps: nat
      ensures !Player1CanWin(SeqToSet(a), SeqToSet(b), steps)
    {
      Player1LosesWithoutMax(SeqToSet(a), SeqToSet(b), maxB, steps);
    }
  }
}

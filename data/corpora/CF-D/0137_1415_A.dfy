ghost predicate InGrid(n: int, m: int, i: int, j: int)
{
  1 <= i <= n && 1 <= j <= m
}

ghost function ReachableWithin(n: int, m: int, ti: int, tj: int, t: int): set<(int, int)>
  requires n >= 1 && m >= 1
  requires InGrid(n, m, ti, tj)
  requires t >= 0
  decreases t
{
  if t == 0 then
    {(ti, tj)}
  else
    var prev := ReachableWithin(n, m, ti, tj, t - 1);
    set i: int, j: int | 1 <= i <= n && 1 <= j <= m &&
      ((i, j) in prev ||
       (i - 1 >= 1 && (i - 1, j) in prev) ||
       (i + 1 <= n && (i + 1, j) in prev) ||
       (j - 1 >= 1 && (i, j - 1) in prev) ||
       (j + 1 <= m && (i, j + 1) in prev))
    :: (i, j)
}

ghost predicate AllReachWithin(n: int, m: int, ti: int, tj: int, t: int)
  requires n >= 1 && m >= 1
  requires InGrid(n, m, ti, tj)
  requires t >= 0
{
  var reach := ReachableWithin(n, m, ti, tj, t);
  forall i, j :: 1 <= i <= n && 1 <= j <= m ==> (i, j) in reach
}

function Abs(x: int): int
{
  if x >= 0 then x else -x
}

lemma ReachableMonotone(n: int, m: int, ti: int, tj: int, t: int, i: int, j: int)
  requires n >= 1 && m >= 1 && InGrid(n, m, ti, tj) && t >= 1
  requires (i, j) in ReachableWithin(n, m, ti, tj, t - 1)
  ensures (i, j) in ReachableWithin(n, m, ti, tj, t)
{
}

lemma ReachableComplete(n: int, m: int, ti: int, tj: int, t: int, i: int, j: int)
  requires n >= 1 && m >= 1 && InGrid(n, m, ti, tj)
  requires InGrid(n, m, i, j) && t >= 0
  requires Abs(i - ti) + Abs(j - tj) <= t
  ensures (i, j) in ReachableWithin(n, m, ti, tj, t)
  decreases t
{
  if t == 0 {
  } else if Abs(i - ti) + Abs(j - tj) <= t - 1 {
    ReachableComplete(n, m, ti, tj, t - 1, i, j);
    ReachableMonotone(n, m, ti, tj, t, i, j);
  } else {
    var prev := ReachableWithin(n, m, ti, tj, t - 1);
    if i > ti {
      assert Abs(i - 1 - ti) + Abs(j - tj) == t - 1;
      ReachableComplete(n, m, ti, tj, t - 1, i - 1, j);
      assert (i - 1, j) in prev;
    } else if i < ti {
      assert Abs(i + 1 - ti) + Abs(j - tj) == t - 1;
      ReachableComplete(n, m, ti, tj, t - 1, i + 1, j);
      assert (i + 1, j) in prev;
    } else if j > tj {
      assert Abs(i - ti) + Abs(j - 1 - tj) == t - 1;
      ReachableComplete(n, m, ti, tj, t - 1, i, j - 1);
      assert (i, j - 1) in prev;
    } else {
      assert i == ti && j < tj;
      assert Abs(i - ti) + Abs(j + 1 - tj) == t - 1;
      ReachableComplete(n, m, ti, tj, t - 1, i, j + 1);
      assert (i, j + 1) in prev;
    }
  }
}

lemma ReachableSoundness(n: int, m: int, ti: int, tj: int, t: int, i: int, j: int)
  requires n >= 1 && m >= 1 && InGrid(n, m, ti, tj) && t >= 0
  requires (i, j) in ReachableWithin(n, m, ti, tj, t)
  ensures Abs(i - ti) + Abs(j - tj) <= t
  decreases t
{
  if t == 0 {
  } else {
    var prev := ReachableWithin(n, m, ti, tj, t - 1);
    if (i, j) in prev {
      ReachableSoundness(n, m, ti, tj, t - 1, i, j);
    } else if i - 1 >= 1 && (i - 1, j) in prev {
      ReachableSoundness(n, m, ti, tj, t - 1, i - 1, j);
    } else if i + 1 <= n && (i + 1, j) in prev {
      ReachableSoundness(n, m, ti, tj, t - 1, i + 1, j);
    } else if j - 1 >= 1 && (i, j - 1) in prev {
      ReachableSoundness(n, m, ti, tj, t - 1, i, j - 1);
    } else {
      assert j + 1 <= m && (i, j + 1) in prev;
      ReachableSoundness(n, m, ti, tj, t - 1, i, j + 1);
    }
  }
}

// Helper: prove AllReachWithin for computed time
lemma AllReachHelper(n: int, m: int, r: int, c: int, dr: int, dc: int, time: int)
  requires n >= 1 && m >= 1 && InGrid(n, m, r, c)
  requires dr >= r - 1 && dr >= n - r
  requires dc >= c - 1 && dc >= m - c
  requires time == dr + dc
  ensures time >= 0
  ensures AllReachWithin(n, m, r, c, time)
{
  forall i, j | 1 <= i <= n && 1 <= j <= m
    ensures (i, j) in ReachableWithin(n, m, r, c, time)
  {
    assert Abs(i - r) <= dr;
    assert Abs(j - c) <= dc;
    ReachableComplete(n, m, r, c, time, i, j);
  }
}

// Helper: prove optimality
lemma OptimalityHelper(n: int, m: int, r: int, c: int, dr: int, dc: int, time: int)
  requires n >= 1 && m >= 1 && InGrid(n, m, r, c)
  requires (dr == r - 1 || dr == n - r) && dr >= r - 1 && dr >= n - r
  requires (dc == c - 1 || dc == m - c) && dc >= c - 1 && dc >= m - c
  requires time == dr + dc && time > 0
  ensures !AllReachWithin(n, m, r, c, time - 1)
{
  var ci := if dr == r - 1 then 1 else n;
  var cj := if dc == c - 1 then 1 else m;
  assert InGrid(n, m, ci, cj);
  assert Abs(ci - r) == dr;
  assert Abs(cj - c) == dc;
  assert Abs(ci - r) + Abs(cj - c) == time;

  if (ci, cj) in ReachableWithin(n, m, r, c, time - 1) {
    ReachableSoundness(n, m, r, c, time - 1, ci, cj);
    assert false;
  }
  assert (ci, cj) !in ReachableWithin(n, m, r, c, time - 1);
}

method PrisonBreak(n: int, m: int, r: int, c: int) returns (time: int)
  requires n >= 1 && m >= 1
  requires InGrid(n, m, r, c)
  ensures time >= 0
  ensures AllReachWithin(n, m, r, c, time)
  ensures time == 0 || !AllReachWithin(n, m, r, c, time - 1)
{
  var dr: int;
  if r - 1 > n - r { dr := r - 1; } else { dr := n - r; }
  var dc: int;
  if c - 1 > m - c { dc := c - 1; } else { dc := m - c; }
  time := dr + dc;

  AllReachHelper(n, m, r, c, dr, dc, time);

  if time > 0 {
    OptimalityHelper(n, m, r, c, dr, dc, time);
  }
}

ghost predicate ChapterNotCompletelyRead(chapter: (int, int), k: int)
{
  exists p | chapter.0 <= p <= chapter.1 :: p >= k
}

ghost function CountNotCompletelyRead(chapters: seq<(int, int)>, k: int): int
  decreases |chapters|
{
  if |chapters| == 0 then 0
  else
    CountNotCompletelyRead(chapters[..|chapters|-1], k)
    + (if ChapterNotCompletelyRead(chapters[|chapters|-1], k) then 1 else 0)
}

lemma ChapterNotCompletelyReadEquiv(chapter: (int, int), k: int)
  requires chapter.0 <= chapter.1
  ensures ChapterNotCompletelyRead(chapter, k) <==> chapter.1 >= k
{
  if chapter.1 >= k {
    assert ChapterNotCompletelyRead(chapter, k) by {
      var w := chapter.1;
      assert chapter.0 <= w <= chapter.1;
      assert w >= k;
    }
  }
}

lemma CountSplit(a: seq<(int, int)>, b: seq<(int, int)>, k: int)
  ensures CountNotCompletelyRead(a + b, k) == CountNotCompletelyRead(a, k) + CountNotCompletelyRead(b, k)
  decreases |b|
{
  if |b| == 0 {
    assert a + b == a;
  } else {
    assert (a + b)[..|a + b| - 1] == a + b[..|b| - 1];
    assert (a + b)[|a + b| - 1] == b[|b| - 1];
    CountSplit(a, b[..|b| - 1], k);
  }
}

lemma AllReadCount(chapters: seq<(int, int)>, k: int)
  requires forall i | 0 <= i < |chapters| :: chapters[i].0 <= chapters[i].1
  requires forall i | 0 <= i < |chapters| :: chapters[i].1 < k
  ensures CountNotCompletelyRead(chapters, k) == 0
  decreases |chapters|
{
  if |chapters| > 0 {
    AllReadCount(chapters[..|chapters| - 1], k);
    ChapterNotCompletelyReadEquiv(chapters[|chapters| - 1], k);
  }
}

lemma AllUnreadCount(chapters: seq<(int, int)>, k: int)
  requires forall i | 0 <= i < |chapters| :: chapters[i].0 <= chapters[i].1
  requires forall i | 0 <= i < |chapters| :: chapters[i].1 >= k
  ensures CountNotCompletelyRead(chapters, k) == |chapters|
  decreases |chapters|
{
  if |chapters| > 0 {
    AllUnreadCount(chapters[..|chapters| - 1], k);
    ChapterNotCompletelyReadEquiv(chapters[|chapters| - 1], k);
  }
}

lemma SortedMonotone(chapters: seq<(int, int)>, i: int, j: int)
  requires forall idx | 0 <= idx < |chapters| :: chapters[idx].0 <= chapters[idx].1
  requires forall idx | 0 <= idx < |chapters| - 1 :: chapters[idx].1 < chapters[idx+1].0
  requires 0 <= i <= j < |chapters|
  ensures chapters[i].1 <= chapters[j].1
  decreases j - i
{
  if i < j {
    SortedMonotone(chapters, i, j - 1);
  }
}

method NastyaBook(chapters: seq<(int, int)>, k: int) returns (count: int)
  requires forall i | 0 <= i < |chapters| :: chapters[i].0 <= chapters[i].1
  requires forall i | 0 <= i < |chapters| - 1 :: chapters[i].1 < chapters[i+1].0
  requires k >= 1
  ensures count == CountNotCompletelyRead(chapters, k)
{
  var i := 0;
  while i < |chapters|
    invariant 0 <= i <= |chapters|
    invariant forall j | 0 <= j < i :: chapters[j].1 < k
  {
    var (_, y) := chapters[i];
    if y >= k {
      forall j | i <= j < |chapters|
        ensures chapters[j].1 >= k
      {
        SortedMonotone(chapters, i, j);
      }

      assert chapters == chapters[..i] + chapters[i..];
      AllReadCount(chapters[..i], k);
      AllUnreadCount(chapters[i..], k);
      CountSplit(chapters[..i], chapters[i..], k);

      count := |chapters| - i;
      return;
    }
    i := i + 1;
  }
  assert chapters[..|chapters|] == chapters;
  AllReadCount(chapters, k);
  count := 0;
  return;
}

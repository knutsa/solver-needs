// --- Specification ---

// Finds the leftmost empty room (smallest index with value 0).
// Returns -1 if no empty room exists.
// Formalizes: "assigned to an empty room closest to the left entrance"
ghost function LeftmostEmpty(rooms: seq<int>): int
  ensures LeftmostEmpty(rooms) == -1 || (0 <= LeftmostEmpty(rooms) < |rooms|)
  decreases |rooms|
{
  if |rooms| == 0 then -1
  else if rooms[0] == 0 then 0
  else
    var rest := LeftmostEmpty(rooms[1..]);
    if rest == -1 then -1 else rest + 1
}

// Finds the rightmost empty room (largest index with value 0).
// Returns -1 if no empty room exists.
// Formalizes: "assigned to an empty room closest to the right entrance"
ghost function RightmostEmpty(rooms: seq<int>): int
  ensures RightmostEmpty(rooms) == -1 || (0 <= RightmostEmpty(rooms) < |rooms|)
  decreases |rooms|
{
  if |rooms| == 0 then -1
  else if rooms[|rooms| - 1] == 0 then |rooms| - 1
  else RightmostEmpty(rooms[..|rooms| - 1])
}

// The hotel state resulting from a single event, per the problem rules:
//   'L': a guest arrives from the left entrance — occupy the leftmost empty room
//   'R': a guest arrives from the right entrance — occupy the rightmost empty room
//   '0'..'9': the guest in that numbered room departs — the room becomes empty
//   Any other character: no change
ghost function HotelAfterEvent(rooms: seq<int>, event: char): seq<int>
  requires |rooms| == 10
  ensures |HotelAfterEvent(rooms, event)| == 10
{
  if event == 'L' then
    var i := LeftmostEmpty(rooms);
    if i == -1 then rooms else rooms[i := 1]
  else if event == 'R' then
    var i := RightmostEmpty(rooms);
    if i == -1 then rooms else rooms[i := 1]
  else if '0' <= event <= '9' then
    rooms[(event as int) - ('0' as int) := 0]
  else
    rooms
}

// The correct hotel room state after processing a sequence of events
// in order, starting from an initially empty hotel (all 10 rooms unoccupied).
ghost function HotelAfterEvents(events: seq<char>): seq<int>
  ensures |HotelAfterEvents(events)| == 10
  decreases |events|
{
  if |events| == 0 then
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
  else
    HotelAfterEvent(HotelAfterEvents(events[..|events| - 1]), events[|events| - 1])
}

// --- Lemmas ---

lemma LeftmostEmptyIs(rooms: seq<int>, i: int)
  requires 0 <= i < |rooms|
  requires rooms[i] == 0
  requires forall j :: 0 <= j < i ==> rooms[j] != 0
  ensures LeftmostEmpty(rooms) == i
  decreases i
{
  if i == 0 {
  } else {
    LeftmostEmptyIs(rooms[1..], i - 1);
  }
}

lemma LeftmostEmptyNone(rooms: seq<int>)
  requires forall j :: 0 <= j < |rooms| ==> rooms[j] != 0
  ensures LeftmostEmpty(rooms) == -1
  decreases |rooms|
{
  if |rooms| == 0 {
  } else {
    LeftmostEmptyNone(rooms[1..]);
  }
}

lemma RightmostEmptyIs(rooms: seq<int>, i: int)
  requires 0 <= i < |rooms|
  requires rooms[i] == 0
  requires forall j :: i < j < |rooms| ==> rooms[j] != 0
  ensures RightmostEmpty(rooms) == i
  decreases |rooms|
{
  if i == |rooms| - 1 {
  } else {
    RightmostEmptyIs(rooms[..|rooms| - 1], i);
  }
}

lemma RightmostEmptyNone(rooms: seq<int>)
  requires forall j :: 0 <= j < |rooms| ==> rooms[j] != 0
  ensures RightmostEmpty(rooms) == -1
  decreases |rooms|
{
  if |rooms| == 0 {
  } else {
    RightmostEmptyNone(rooms[..|rooms| - 1]);
  }
}

// --- Implementation ---

method Hotelier(events: seq<char>) returns (rooms: seq<int>)
  ensures |rooms| == 10
  ensures rooms == HotelAfterEvents(events)
{
  rooms := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
  var idx := 0;
  while idx < |events|
    invariant 0 <= idx <= |events|
    invariant |rooms| == 10
    invariant rooms == HotelAfterEvents(events[..idx])
  {
    ghost var old_rooms := rooms;
    var ch := events[idx];
    if ch == 'L' {
      var i := 0;
      var found := false;
      while i < 10 && !found
        invariant 0 <= i <= 10
        invariant |rooms| == 10
        invariant !found ==> rooms == old_rooms
        invariant !found ==> forall j :: 0 <= j < i ==> old_rooms[j] != 0
        invariant found ==> rooms == HotelAfterEvent(old_rooms, 'L')
        decreases !found, 10 - i
      {
        if rooms[i] == 0 {
          LeftmostEmptyIs(old_rooms, i);
          rooms := rooms[i := 1];
          found := true;
        } else {
          i := i + 1;
        }
      }
      if !found {
        LeftmostEmptyNone(old_rooms);
      }
    } else if ch == 'R' {
      var i := 9;
      var found := false;
      while i >= 0 && !found
        invariant -1 <= i <= 9
        invariant |rooms| == 10
        invariant !found ==> rooms == old_rooms
        invariant !found ==> forall j :: i < j < 10 ==> old_rooms[j] != 0
        invariant found ==> rooms == HotelAfterEvent(old_rooms, 'R')
        decreases !found, i + 1
      {
        if rooms[i] == 0 {
          RightmostEmptyIs(old_rooms, i);
          rooms := rooms[i := 1];
          found := true;
        } else {
          i := i - 1;
        }
      }
      if !found {
        RightmostEmptyNone(old_rooms);
      }
    } else if '0' <= ch <= '9' {
      var i := (ch as int) - ('0' as int);
      rooms := rooms[i := 0];
    }
    assert rooms == HotelAfterEvent(old_rooms, ch);
    assert events[..idx + 1][..idx] == events[..idx];
    idx := idx + 1;
  }
  assert events[..idx] == events;
}

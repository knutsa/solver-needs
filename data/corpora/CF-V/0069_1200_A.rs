use vstd::prelude::*;

verus! {

// --- Specification ---

pub open spec fn leftmost_empty(rooms: Seq<int>) -> int
    decreases rooms.len(),
{
    if rooms.len() == 0 {
        -1int
    } else if rooms[0] == 0 {
        0int
    } else {
        let rest = leftmost_empty(rooms.subrange(1, rooms.len() as int));
        if rest == -1 { -1int } else { rest + 1 }
    }
}

pub open spec fn rightmost_empty(rooms: Seq<int>) -> int
    decreases rooms.len(),
{
    if rooms.len() == 0 {
        -1int
    } else if rooms[rooms.len() as int - 1] == 0 {
        rooms.len() as int - 1
    } else {
        rightmost_empty(rooms.subrange(0, rooms.len() as int - 1))
    }
}

pub proof fn leftmost_empty_bounds(rooms: Seq<int>)
    ensures
        leftmost_empty(rooms) == -1 || (0 <= leftmost_empty(rooms) && leftmost_empty(rooms) < rooms.len() as int),
    decreases rooms.len(),
{
    if rooms.len() == 0 {
    } else if rooms[0] == 0 {
    } else {
        leftmost_empty_bounds(rooms.subrange(1, rooms.len() as int));
    }
}

pub proof fn rightmost_empty_bounds(rooms: Seq<int>)
    ensures
        rightmost_empty(rooms) == -1 || (0 <= rightmost_empty(rooms) && rightmost_empty(rooms) < rooms.len() as int),
    decreases rooms.len(),
{
    if rooms.len() == 0 {
    } else if rooms[rooms.len() as int - 1] == 0 {
    } else {
        rightmost_empty_bounds(rooms.subrange(0, rooms.len() as int - 1));
    }
}

// event encoded as int: 'L' = 76, 'R' = 82, '0'..'9' = 48..57
pub open spec fn hotel_after_event(rooms: Seq<int>, event: int) -> Seq<int>
    recommends rooms.len() == 10,
{
    if event == 76 {  // 'L'
        let i = leftmost_empty(rooms);
        if i == -1 { rooms } else { rooms.update(i, 1int) }
    } else if event == 82 {  // 'R'
        let i = rightmost_empty(rooms);
        if i == -1 { rooms } else { rooms.update(i, 1int) }
    } else if 48 <= event && event <= 57 {  // '0'..'9'
        rooms.update(event - 48, 0int)
    } else {
        rooms
    }
}

pub proof fn hotel_after_event_len(rooms: Seq<int>, event: int)
    requires rooms.len() == 10,
    ensures hotel_after_event(rooms, event).len() == 10,
{
    leftmost_empty_bounds(rooms);
    rightmost_empty_bounds(rooms);
}

pub open spec fn hotel_after_events(events: Seq<int>) -> Seq<int>
    decreases events.len(),
{
    if events.len() == 0 {
        seq![0int, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    } else {
        let prev = hotel_after_events(events.subrange(0, events.len() as int - 1));
        hotel_after_event(prev, events[events.len() as int - 1])
    }
}

pub proof fn hotel_after_events_len(events: Seq<int>)
    ensures hotel_after_events(events).len() == 10,
    decreases events.len(),
{
    if events.len() == 0 {
    } else {
        hotel_after_events_len(events.subrange(0, events.len() as int - 1));
        hotel_after_event_len(
            hotel_after_events(events.subrange(0, events.len() as int - 1)),
            events[events.len() as int - 1],
        );
    }
}

// --- Lemmas ---

pub proof fn leftmost_empty_is(rooms: Seq<int>, i: int)
    requires
        0 <= i && i < rooms.len() as int,
        rooms[i] == 0,
        forall|j: int| 0 <= j && j < i ==> rooms[j] != 0,
    ensures
        leftmost_empty(rooms) == i,
    decreases i,
{
    if i == 0 {
    } else {
        assert(rooms[0] != 0);
        let sub = rooms.subrange(1, rooms.len() as int);
        assert forall|j: int| 0 <= j && j < i - 1 implies sub[j] != 0 by {
            assert(sub[j] == rooms[j + 1]);
            assert(rooms[j + 1] != 0);
        }
        assert(sub[i - 1] == rooms[i]);
        leftmost_empty_is(sub, i - 1);
    }
}

pub proof fn leftmost_empty_none(rooms: Seq<int>)
    requires
        forall|j: int| 0 <= j && j < rooms.len() as int ==> rooms[j] != 0,
    ensures
        leftmost_empty(rooms) == -1,
    decreases rooms.len(),
{
    if rooms.len() == 0 {
    } else {
        assert(rooms[0] != 0);
        let sub = rooms.subrange(1, rooms.len() as int);
        assert forall|j: int| 0 <= j && j < sub.len() as int implies sub[j] != 0 by {
            assert(sub[j] == rooms[j + 1]);
        }
        leftmost_empty_none(sub);
    }
}

pub proof fn rightmost_empty_is(rooms: Seq<int>, i: int)
    requires
        0 <= i && i < rooms.len() as int,
        rooms[i] == 0,
        forall|j: int| i < j && j < rooms.len() as int ==> rooms[j] != 0,
    ensures
        rightmost_empty(rooms) == i,
    decreases rooms.len(),
{
    if i == rooms.len() as int - 1 {
    } else {
        assert(rooms[rooms.len() as int - 1] != 0);
        let sub = rooms.subrange(0, rooms.len() as int - 1);
        assert forall|j: int| i < j && j < sub.len() as int implies sub[j] != 0 by {
            assert(sub[j] == rooms[j]);
        }
        assert(sub[i] == rooms[i]);
        rightmost_empty_is(sub, i);
    }
}

pub proof fn rightmost_empty_none(rooms: Seq<int>)
    requires
        forall|j: int| 0 <= j && j < rooms.len() as int ==> rooms[j] != 0,
    ensures
        rightmost_empty(rooms) == -1,
    decreases rooms.len(),
{
    if rooms.len() == 0 {
    } else {
        assert(rooms[rooms.len() as int - 1] != 0);
        let sub = rooms.subrange(0, rooms.len() as int - 1);
        assert forall|j: int| 0 <= j && j < sub.len() as int implies sub[j] != 0 by {
            assert(sub[j] == rooms[j]);
        }
        rightmost_empty_none(sub);
    }
}

// --- Implementation ---

// We use Vec<i64> for both events and rooms in exec code.
// In spec, events are Seq<int> and rooms are Seq<int>.
pub fn hotelier(events: &Vec<i64>) -> (rooms: Vec<i64>)
    ensures
        rooms@.len() == 10,
        rooms@.map_values(|v: i64| v as int) =~= hotel_after_events(events@.map_values(|e: i64| e as int)),
{
    let mut rooms: Vec<i64> = vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let mut idx: usize = 0;

    let ghost events_spec: Seq<int> = events@.map_values(|e: i64| e as int);

    while idx < events.len()
        invariant
            0 <= idx <= events.len(),
            rooms@.len() == 10,
            events_spec =~= events@.map_values(|e: i64| e as int),
            rooms@.map_values(|v: i64| v as int) =~= hotel_after_events(events_spec.subrange(0, idx as int)),
        decreases events.len() - idx,
    {
        let ghost old_rooms_spec: Seq<int> = rooms@.map_values(|v: i64| v as int);
        let ch = events[idx];
        let ghost ch_spec: int = ch as int;

        if ch == 76 {  // 'L'
            let mut i: usize = 0;
            let mut found: bool = false;
            while i < 10 && !found
                invariant
                    0 <= i <= 10,
                    rooms@.len() == 10,
                    !found ==> rooms@.map_values(|v: i64| v as int) =~= old_rooms_spec,
                    !found ==> (forall|j: int| 0 <= j && j < (i as int) ==> old_rooms_spec[j] != 0),
                    found ==> rooms@.map_values(|v: i64| v as int) =~= hotel_after_event(old_rooms_spec, 76int),
                decreases 10 - i + if found { 0usize } else { 1usize },
            {
                if rooms[i] == 0 {
                    proof {
                        leftmost_empty_is(old_rooms_spec, i as int);
                    }
                    rooms.set(i, 1);
                    found = true;
                } else {
                    i = i + 1;
                }
            }
            if !found {
                proof {
                    leftmost_empty_none(old_rooms_spec);
                }
            }
        } else if ch == 82 {  // 'R'
            let mut i: i64 = 9;
            let mut found: bool = false;
            while i >= 0 && !found
                invariant
                    -1 <= i <= 9,
                    rooms@.len() == 10,
                    !found ==> rooms@.map_values(|v: i64| v as int) =~= old_rooms_spec,
                    !found ==> (forall|j: int| (i as int) < j && j < 10 ==> old_rooms_spec[j] != 0),
                    found ==> rooms@.map_values(|v: i64| v as int) =~= hotel_after_event(old_rooms_spec, 82int),
                decreases (i + 1) + if found { 0int } else { 1int },
            {
                if rooms[i as usize] == 0 {
                    proof {
                        rightmost_empty_is(old_rooms_spec, i as int);
                    }
                    rooms.set(i as usize, 1);
                    found = true;
                } else {
                    i = i - 1;
                }
            }
            if !found {
                proof {
                    rightmost_empty_none(old_rooms_spec);
                }
            }
        } else if ch >= 48 && ch <= 57 {  // '0'..'9'
            let i: usize = (ch - 48) as usize;
            rooms.set(i, 0);
        }

        proof {
            hotel_after_events_len(events_spec.subrange(0, idx as int));
            assert(rooms@.map_values(|v: i64| v as int) =~= hotel_after_event(old_rooms_spec, ch_spec));

            let prefix = events_spec.subrange(0, idx as int);
            let prefix_plus = events_spec.subrange(0, idx as int + 1);
            assert(prefix_plus.subrange(0, prefix_plus.len() as int - 1) =~= prefix);
            assert(prefix_plus[prefix_plus.len() as int - 1] == ch_spec);
            assert(hotel_after_events(prefix_plus) =~= hotel_after_event(
                hotel_after_events(prefix),
                ch_spec,
            ));
            assert(rooms@.map_values(|v: i64| v as int) =~= hotel_after_events(prefix_plus));
        }

        idx = idx + 1;
    }

    proof {
        assert(events_spec.subrange(0, idx as int) =~= events_spec);
    }

    rooms
}

fn main() {}

} // verus!

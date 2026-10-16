use vstd::prelude::*;

verus! {

pub open spec fn count_val(s: Seq<i64>, v: i64) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0int
    } else {
        count_val(s.take(s.len() as int - 1), v) + if s[s.len() as int - 1] == v { 1int } else { 0int }
    }
}

pub open spec fn can_exit_after(doors: Seq<i64>, k: int) -> bool
    recommends 0 <= k <= doors.len(),
{
    count_val(doors.take(k), 0) == count_val(doors, 0) ||
    count_val(doors.take(k), 1) == count_val(doors, 1)
}

proof fn lemma_count_val_step(s: Seq<i64>, i: int, v: i64)
    requires 0 <= i < s.len(),
    ensures count_val(s.take(i + 1), v) == count_val(s.take(i), v) + if s[i] == v { 1int } else { 0int },
{
    let t = s.take(i + 1);
    assert(t.take(t.len() as int - 1) =~= s.take(i));
}

proof fn lemma_take_all(s: Seq<i64>)
    ensures s.take(s.len() as int) =~= s,
{
    assert(s.take(s.len() as int) =~= s);
}

proof fn lemma_count_val_ext(a: Seq<i64>, b: Seq<i64>, v: i64)
    requires a =~= b,
    ensures count_val(a, v) == count_val(b, v),
    decreases a.len(),
{
    if a.len() > 0 {
        assert(a.take(a.len() as int - 1) =~= b.take(b.len() as int - 1));
        lemma_count_val_ext(a.take(a.len() as int - 1), b.take(b.len() as int - 1), v);
    }
}

fn the_doors(n: usize, doors: &Vec<i64>) -> (k: usize)
    requires
        n == doors@.len(),
        n >= 2,
        n < usize::MAX,
        forall|i: int| #![auto] 0 <= i < n as int ==> (doors@[i] == 0 || doors@[i] == 1),
        count_val(doors@, 0) >= 1,
        count_val(doors@, 1) >= 1,
    ensures
        1 <= k <= n,
        can_exit_after(doors@, k as int),
        forall|j: int| 0 <= j < k as int ==> !#[trigger] can_exit_after(doors@, j),
{
    let ghost s = doors@;

    // First loop: count total 0s and 1s
    let mut a: usize = 0;
    let mut b: usize = 0;
    let mut i: usize = 0;

    proof {
        assert(s.take(0int) =~= Seq::<i64>::empty());
    }

    while i < n
        invariant
            0 <= i <= n,
            n == doors@.len(),
            n < usize::MAX,
            s =~= doors@,
            a as int == count_val(s.take(i as int), 0),
            b as int == count_val(s.take(i as int), 1),
            forall|j: int| #![auto] 0 <= j < n as int ==> (s[j] == 0 || s[j] == 1),
            a <= i,
            b <= i,
            a + b == i,
        decreases n - i,
    {
        proof {
            lemma_count_val_step(s, i as int, 0);
            lemma_count_val_step(s, i as int, 1);
        }
        let di = doors[i];
        if di == 0 {
            a = a + 1;
        } else {
            b = b + 1;
        }
        i = i + 1;
    }

    proof {
        lemma_take_all(s);
    }

    // Second loop: find first exit
    let mut x: usize = 0;
    let mut y: usize = 0;
    i = 0;

    proof {
        assert(s.take(0int) =~= Seq::<i64>::empty());
        assert(count_val(s.take(0int), 0) == 0);
        assert(count_val(s.take(0int), 1) == 0);
        assert(!can_exit_after(s, 0int));
    }

    while i < n
        invariant
            0 <= i <= n,
            n == doors@.len(),
            n >= 2,
            n < usize::MAX,
            s =~= doors@,
            x as int == count_val(s.take(i as int), 0),
            y as int == count_val(s.take(i as int), 1),
            a as int == count_val(s, 0),
            b as int == count_val(s, 1),
            forall|j: int| #![auto] 0 <= j < n as int ==> (s[j] == 0 || s[j] == 1),
            forall|j: int| 0 <= j <= i as int ==> !#[trigger] can_exit_after(s, j),
            count_val(s, 0) >= 1,
            count_val(s, 1) >= 1,
            x <= i,
            y <= i,
            x + y == i,
        decreases n - i,
    {
        proof {
            lemma_count_val_step(s, i as int, 0);
            lemma_count_val_step(s, i as int, 1);
        }
        let di = doors[i];
        if di == 1 {
            y = y + 1;
        } else {
            x = x + 1;
        }

        if x == a || y == b {
            proof {
                assert(can_exit_after(s, (i + 1) as int));
            }
            return (i + 1);
        }

        proof {
            assert(!can_exit_after(s, (i + 1) as int));
        }
        i = i + 1;
    }

    proof {
        lemma_take_all(s);
        assert(s.take(n as int) =~= s);
        lemma_count_val_ext(s.take(n as int), s, 0);
        lemma_count_val_ext(s.take(n as int), s, 1);
        // Now: count_val(s.take(n), 0) == count_val(s, 0) == a
        // And: x == count_val(s.take(n), 0) from invariant (i == n)
        assert(x as int == count_val(s.take(n as int), 0));
        assert(count_val(s.take(n as int), 0) == count_val(s, 0));
        assert(a as int == count_val(s, 0));
        // So x == a
        assert(x as int == a as int);
        // But the loop body checks x == a and returns. If we got here, we never returned,
        // which means on the last iteration i = n-1, after the step, x+y == n and x == a.
        // But we checked x == a and it was true, so we would have returned. Contradiction.
        // Actually the contradiction is simpler: if x == a after the loop, then
        // can_exit_after(s, n) is true (since count_val(s.take(n), 0) == count_val(s, 0)),
        // but the invariant says !can_exit_after(s, j) for j <= i == n.
        // Let's assert can_exit_after and its negation.
        assert(can_exit_after(s, n as int));
        assert(!can_exit_after(s, n as int));
    }
    return 0;
}

fn main() {}

} // verus!

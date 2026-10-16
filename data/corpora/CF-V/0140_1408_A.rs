use vstd::prelude::*;

verus! {

spec fn valid_input(n: int, a: Seq<int>, b: Seq<int>, c: Seq<int>) -> bool {
    n >= 3
    && a.len() == n
    && b.len() == n
    && c.len() == n
    && forall|i: int| 0 <= i < n ==> (
        #[trigger] a[i] != b[i]
        && a[i] != c[i]
        && b[i] != c[i]
    )
}

spec fn chosen_from_options(p: Seq<int>, a: Seq<int>, b: Seq<int>, c: Seq<int>) -> bool
    recommends p.len() == a.len() == b.len() == c.len()
{
    forall|i: int| 0 <= i < p.len() ==> (
        #[trigger] p[i] == a[i]
        || p[i] == b[i]
        || p[i] == c[i]
    )
}

spec fn no_adjacent_equal(p: Seq<int>) -> bool
    recommends p.len() >= 1
{
    (forall|i: int| 0 <= i < p.len() - 1 ==> #[trigger] p[i] != p[i + 1])
    && p[p.len() - 1] != p[0]
}

spec fn valid_coloring(p: Seq<int>, n: int, a: Seq<int>, b: Seq<int>, c: Seq<int>) -> bool {
    p.len() == n
    && n >= 3
    && a.len() == n
    && b.len() == n
    && c.len() == n
    && chosen_from_options(p, a, b, c)
    && no_adjacent_equal(p)
}

spec fn to_int(s: Seq<i64>) -> Seq<int> {
    s.map(|_i: int, x: i64| x as int)
}

proof fn to_int_index(s: Seq<i64>, i: int)
    requires 0 <= i < s.len(),
    ensures to_int(s)[i] == s[i] as int,
{
}

proof fn to_int_len(s: Seq<i64>)
    ensures to_int(s).len() == s.len(),
{
}

fn circle_coloring(n: i64, a: &Vec<i64>, b: &Vec<i64>, c: &Vec<i64>) -> (p: Vec<i64>)
    requires
        valid_input(n as int, to_int(a@), to_int(b@), to_int(c@)),
        a.len() == n as usize,
        b.len() == n as usize,
        c.len() == n as usize,
        n >= 3,
        n < 0x7FFF_FFFF_FFFF_FFFF,
    ensures
        valid_coloring(to_int(p@), n as int, to_int(a@), to_int(b@), to_int(c@)),
{
    let n_us = n as usize;

    let mut out: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < n_us
        invariant
            out.len() == idx,
            idx <= n_us,
            n_us == n as usize,
        decreases n_us - idx,
    {
        out.push(0);
        idx += 1;
    }

    // out[0] = a[0]
    out.set(0, a[0]);

    // Elements 1..n-2: pick one that differs from previous
    let mut i: usize = 1;
    while i < n_us - 1
        invariant
            1 <= i <= n_us - 1,
            out.len() == n_us,
            a.len() == n_us,
            b.len() == n_us,
            c.len() == n_us,
            n >= 3,
            n_us == n as usize,
            n_us < 0x7FFF_FFFF_FFFF_FFFF,
            valid_input(n as int, to_int(a@), to_int(b@), to_int(c@)),
            // Chosen from options for indices 0..i
            forall|j: int| #![trigger out@[j]] 0 <= j < i as int ==> (
                out@[j] == a@[j]
                || out@[j] == b@[j]
                || out@[j] == c@[j]
            ),
            // No adjacent equal for indices 0..i
            forall|j: int| #![trigger out@[j]] 1 <= j < i as int ==>
                out@[j] != out@[j - 1],
        decreases n_us - 1 - i,
    {
        if a[i] != out[i - 1] {
            out.set(i, a[i]);
            assert(out@[i as int] == a@[i as int]);
            assert(out@[i as int] != out@[i as int - 1]) by {
                // a[i] != out[i-1] was the branch condition
            }
        } else {
            // a[i] == out[i-1] and a[i] != b[i] (from valid_input), so b[i] != out[i-1]
            proof {
                to_int_index(a@, i as int);
                to_int_index(b@, i as int);
                to_int_index(out@, i as int - 1);
                // valid_input says a[i] != b[i]
                assert(to_int(a@)[i as int] != to_int(b@)[i as int]);
                // So a@[i] != b@[i] as i64 values
            }
            out.set(i, b[i]);
            assert(out@[i as int] == b@[i as int]);
        }

        // Prove invariants maintained for all j
        assert forall|j: int| #![trigger out@[j]] 0 <= j < (i + 1) as int implies (
            out@[j] == a@[j]
            || out@[j] == b@[j]
            || out@[j] == c@[j]
        ) by {}

        assert forall|j: int| #![trigger out@[j]] 1 <= j < (i + 1) as int implies
            out@[j] != out@[j - 1]
        by {}

        i += 1;
    }

    // Last element: must differ from both out[n-2] and out[0]
    if a[n_us - 1] != out[n_us - 2] && a[n_us - 1] != out[0] {
        out.set(n_us - 1, a[n_us - 1]);
    } else if b[n_us - 1] != out[n_us - 2] && b[n_us - 1] != out[0] {
        out.set(n_us - 1, b[n_us - 1]);
    } else {
        // Both a and b are "blocked" by out[n-2] or out[0].
        // Since a[n-1] != b[n-1] (valid_input), they cover both forbidden values.
        // Since c[n-1] != a[n-1] and c[n-1] != b[n-1], c avoids both.
        proof {
            to_int_index(a@, n as int - 1);
            to_int_index(b@, n as int - 1);
            to_int_index(c@, n as int - 1);
            to_int_index(out@, n as int - 2);
            to_int_index(out@, 0);
        }
        assert(a[n_us - 1] == out[n_us - 2] || a[n_us - 1] == out[0]);
        assert(b[n_us - 1] == out[n_us - 2] || b[n_us - 1] == out[0]);
        out.set(n_us - 1, c[n_us - 1]);
    }

    proof {
        // Prove chosen_from_options
        assert forall|j: int| 0 <= j < to_int(out@).len() implies (
            #[trigger] to_int(out@)[j] == to_int(a@)[j]
            || to_int(out@)[j] == to_int(b@)[j]
            || to_int(out@)[j] == to_int(c@)[j]
        ) by {
            to_int_index(out@, j);
            to_int_index(a@, j);
            to_int_index(b@, j);
            to_int_index(c@, j);
            // We know out@[j] == a@[j] || out@[j] == b@[j] || out@[j] == c@[j]
            // Therefore (out@[j] as int) equals one of (a@[j] as int), (b@[j] as int), (c@[j] as int)
        }

        // Prove no_adjacent_equal: consecutive pairs
        assert forall|j: int| 0 <= j < to_int(out@).len() - 1 implies (
            #[trigger] to_int(out@)[j] != to_int(out@)[j + 1]
        ) by {
            to_int_index(out@, j);
            to_int_index(out@, j + 1);
            // We know out@[j] != out@[j+1] (equivalently out@[j+1] != out@[j])
            // Need to show the j = n-2 case: out[n-2] != out[n-1]
        }

        // Prove wrap-around: last != first
        to_int_index(out@, to_int(out@).len() - 1);
        to_int_index(out@, 0);
        assert(to_int(out@)[to_int(out@).len() - 1] != to_int(out@)[0]);
    }

    out
}

fn main() {}

} // verus!

use vstd::prelude::*;

verus! {

// --- Spec functions ---

pub open spec fn count_even(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_even(s.subrange(0, s.len() as int - 1)) + if s[s.len() as int - 1] % 2 == 0 { 1int } else { 0int }
    }
}

pub open spec fn count_odd(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_odd(s.subrange(0, s.len() as int - 1)) + if s[s.len() as int - 1] % 2 != 0 { 1int } else { 0int }
    }
}

pub open spec fn spec_min(x: int, y: int) -> int {
    if x <= y { x } else { y }
}

pub open spec fn even_indices(s: Seq<int>) -> Seq<int>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        even_indices(s.subrange(0, s.len() as int - 1)) + if s[s.len() as int - 1] % 2 == 0 {
            seq![s.len() as int - 1]
        } else {
            Seq::<int>::empty()
        }
    }
}

pub open spec fn odd_indices(s: Seq<int>) -> Seq<int>
    decreases s.len(),
{
    if s.len() == 0 {
        Seq::empty()
    } else {
        odd_indices(s.subrange(0, s.len() as int - 1)) + if s[s.len() as int - 1] % 2 != 0 {
            seq![s.len() as int - 1]
        } else {
            Seq::<int>::empty()
        }
    }
}

pub open spec fn zip(xs: Seq<int>, ys: Seq<int>) -> Seq<(int, int)>
    decreases xs.len(),
{
    if xs.len() == 0 || ys.len() == 0 {
        Seq::empty()
    } else {
        seq![(xs[0], ys[0])] + zip(xs.subrange(1, xs.len() as int), ys.subrange(1, ys.len() as int))
    }
}

pub open spec fn is_valid_matching(a: Seq<int>, b: Seq<int>, m: Seq<(int, int)>) -> bool {
    (forall|k: int| 0 <= k < m.len() ==> (
        0 <= #[trigger] m[k].0 < a.len()
        && 0 <= m[k].1 < b.len()
        && (a[m[k].0] + b[m[k].1]) % 2 == 1
    ))
    && (forall|i: int, j: int| 0 <= i < j < m.len() ==> #[trigger] m[i].0 != #[trigger] m[j].0)
    && (forall|i: int, j: int| 0 <= i < j < m.len() ==> #[trigger] m[i].1 != #[trigger] m[j].1)
}

pub open spec fn witness_matching(a: Seq<int>, b: Seq<int>) -> Seq<(int, int)> {
    zip(even_indices(a), odd_indices(b)) + zip(odd_indices(a), even_indices(b))
}

pub open spec fn matching_upper_bound(a: Seq<int>, b: Seq<int>) -> int {
    spec_min(count_even(a), count_odd(b)) + spec_min(count_odd(a), count_even(b))
}

// --- Helper lemmas ---

proof fn even_indices_properties(s: Seq<int>)
    ensures
        even_indices(s).len() == count_even(s),
        forall|k: int| 0 <= k < even_indices(s).len() ==> 0 <= #[trigger] even_indices(s)[k] < s.len(),
        forall|k: int| 0 <= k < even_indices(s).len() ==> #[trigger] s[even_indices(s)[k]] % 2 == 0,
        forall|i: int, j: int| 0 <= i < j < even_indices(s).len() ==> #[trigger] even_indices(s)[i] < #[trigger] even_indices(s)[j],
    decreases s.len(),
{
    if s.len() > 0 {
        let prefix = s.subrange(0, s.len() as int - 1);
        even_indices_properties(prefix);
        let ei_prefix = even_indices(prefix);
        // The key insight: s and prefix agree on all indices < s.len() - 1
        assert forall|k: int| 0 <= k < ei_prefix.len() implies #[trigger] s[ei_prefix[k]] % 2 == 0 by {
            assert(prefix[ei_prefix[k]] == s[ei_prefix[k]]);
        };
    }
}

proof fn odd_indices_properties(s: Seq<int>)
    ensures
        odd_indices(s).len() == count_odd(s),
        forall|k: int| 0 <= k < odd_indices(s).len() ==> 0 <= #[trigger] odd_indices(s)[k] < s.len(),
        forall|k: int| 0 <= k < odd_indices(s).len() ==> #[trigger] s[odd_indices(s)[k]] % 2 != 0,
        forall|i: int, j: int| 0 <= i < j < odd_indices(s).len() ==> #[trigger] odd_indices(s)[i] < #[trigger] odd_indices(s)[j],
    decreases s.len(),
{
    if s.len() > 0 {
        let prefix = s.subrange(0, s.len() as int - 1);
        odd_indices_properties(prefix);
        let oi_prefix = odd_indices(prefix);
        assert forall|k: int| 0 <= k < oi_prefix.len() implies #[trigger] s[oi_prefix[k]] % 2 != 0 by {
            assert(prefix[oi_prefix[k]] == s[oi_prefix[k]]);
        };
    }
}

proof fn zip_length(xs: Seq<int>, ys: Seq<int>)
    ensures zip(xs, ys).len() == spec_min(xs.len() as int, ys.len() as int)
    decreases xs.len(),
{
    if xs.len() > 0 && ys.len() > 0 {
        zip_length(xs.subrange(1, xs.len() as int), ys.subrange(1, ys.len() as int));
    }
}

proof fn zip_element(xs: Seq<int>, ys: Seq<int>, k: int)
    requires 0 <= k < spec_min(xs.len() as int, ys.len() as int)
    ensures
        k < zip(xs, ys).len(),
        zip(xs, ys)[k] == (xs[k], ys[k]),
    decreases xs.len(),
{
    zip_length(xs, ys);
    if k > 0 {
        zip_element(xs.subrange(1, xs.len() as int), ys.subrange(1, ys.len() as int), k - 1);
    }
}

proof fn witness_matching_is_valid(a: Seq<int>, b: Seq<int>)
    ensures
        is_valid_matching(a, b, witness_matching(a, b)),
        witness_matching(a, b).len() == matching_upper_bound(a, b),
{
    let ea = even_indices(a);
    let ob = odd_indices(b);
    let oa = odd_indices(a);
    let eb = even_indices(b);

    even_indices_properties(a);
    odd_indices_properties(b);
    odd_indices_properties(a);
    even_indices_properties(b);

    zip_length(ea, ob);
    zip_length(oa, eb);

    let p1 = zip(ea, ob);
    let p2 = zip(oa, eb);
    let m = p1 + p2;

    assert(m =~= witness_matching(a, b));

    // Establish element access for Zip results
    assert forall|k: int| 0 <= k < p1.len() implies #[trigger] p1[k] == (ea[k], ob[k]) by {
        zip_element(ea, ob, k);
    };

    assert forall|k: int| 0 <= k < p2.len() implies #[trigger] p2[k] == (oa[k], eb[k]) by {
        zip_element(oa, eb, k);
    };

    // Each pair has valid indices and odd sum
    assert forall|k: int| 0 <= k < m.len() implies (
        0 <= #[trigger] m[k].0 < a.len()
        && 0 <= m[k].1 < b.len()
        && (a[m[k].0] + b[m[k].1]) % 2 == 1
    ) by {
        if k < p1.len() {
            assert(m[k] == p1[k]);
            assert(p1[k] == (ea[k], ob[k]));
        } else {
            let idx = k - p1.len() as int;
            assert(m[k] == p2[idx]);
            assert(p2[idx] == (oa[idx], eb[idx]));
        }
    };

    // No duplicate chest indices
    assert forall|i: int, j: int| 0 <= i < j < m.len() implies #[trigger] m[i].0 != #[trigger] m[j].0 by {
        if i < p1.len() && j < p1.len() {
            assert(m[i].0 == ea[i] && m[j].0 == ea[j]);
        } else if i >= p1.len() {
            let ii = i - p1.len() as int;
            let jj = j - p1.len() as int;
            assert(m[i].0 == oa[ii] && m[j].0 == oa[jj]);
        } else {
            assert(a[m[i].0] % 2 == 0 && a[m[j].0] % 2 != 0);
        }
    };

    // No duplicate key indices
    assert forall|i: int, j: int| 0 <= i < j < m.len() implies #[trigger] m[i].1 != #[trigger] m[j].1 by {
        if i < p1.len() && j < p1.len() {
            assert(m[i].1 == ob[i] && m[j].1 == ob[j]);
        } else if i >= p1.len() {
            let ii = i - p1.len() as int;
            let jj = j - p1.len() as int;
            assert(m[i].1 == eb[ii] && m[j].1 == eb[jj]);
        } else {
            assert(b[m[i].1] % 2 != 0 && b[m[j].1] % 2 == 0);
        }
    };
}

fn neko_finds_grapes(a: &Vec<i64>, b: &Vec<i64>) -> (max_chests: i64)
    requires
        a@.len() <= i64::MAX,
        b@.len() <= i64::MAX,
        a@.len() + b@.len() <= i64::MAX,
    ensures
        is_valid_matching(a@.map(|_i, x: i64| x as int), b@.map(|_i, x: i64| x as int),
            witness_matching(a@.map(|_i, x: i64| x as int), b@.map(|_i, x: i64| x as int))),
        witness_matching(a@.map(|_i, x: i64| x as int), b@.map(|_i, x: i64| x as int)).len() == max_chests,
        max_chests == matching_upper_bound(a@.map(|_i, x: i64| x as int), b@.map(|_i, x: i64| x as int)),
{
    let ghost a_spec = a@.map(|_i, x: i64| x as int);
    let ghost b_spec = b@.map(|_i, x: i64| x as int);

    let mut a0: i64 = 0;
    let mut a1: i64 = 0;
    let mut b0: i64 = 0;
    let mut b1: i64 = 0;

    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a@.len() <= i64::MAX,
            b@.len() <= i64::MAX,
            a@.len() + b@.len() <= i64::MAX,
            a0 == count_even(a_spec.subrange(0, i as int)),
            a1 == count_odd(a_spec.subrange(0, i as int)),
            a0 >= 0,
            a1 >= 0,
            a0 + a1 == i,
            a_spec == a@.map(|_i, x: i64| x as int),
        decreases a.len() - i,
    {
        proof {
            let s_new = a_spec.subrange(0, i as int + 1);
            assert(s_new =~= a_spec.subrange(0, i as int).push(a_spec[i as int]));
            assert(s_new.subrange(0, s_new.len() as int - 1) =~= a_spec.subrange(0, i as int));
            assert(s_new[s_new.len() as int - 1] == a_spec[i as int]);
        }
        if a[i] % 2 == 0 {
            a0 = a0 + 1;
        } else {
            a1 = a1 + 1;
        }
        i = i + 1;
    }
    proof {
        assert(a_spec.subrange(0, a_spec.len() as int) =~= a_spec);
    }

    i = 0;
    while i < b.len()
        invariant
            0 <= i <= b.len(),
            a@.len() <= i64::MAX,
            b@.len() <= i64::MAX,
            a@.len() + b@.len() <= i64::MAX,
            b0 == count_even(b_spec.subrange(0, i as int)),
            b1 == count_odd(b_spec.subrange(0, i as int)),
            b0 >= 0,
            b1 >= 0,
            b0 + b1 == i,
            b_spec == b@.map(|_i, x: i64| x as int),
            a0 == count_even(a_spec),
            a1 == count_odd(a_spec),
            a0 >= 0,
            a1 >= 0,
            a_spec == a@.map(|_i, x: i64| x as int),
        decreases b.len() - i,
    {
        proof {
            let s_new = b_spec.subrange(0, i as int + 1);
            assert(s_new =~= b_spec.subrange(0, i as int).push(b_spec[i as int]));
            assert(s_new.subrange(0, s_new.len() as int - 1) =~= b_spec.subrange(0, i as int));
            assert(s_new[s_new.len() as int - 1] == b_spec[i as int]);
        }
        if b[i] % 2 == 0 {
            b0 = b0 + 1;
        } else {
            b1 = b1 + 1;
        }
        i = i + 1;
    }
    proof {
        assert(b_spec.subrange(0, b_spec.len() as int) =~= b_spec);
    }

    let x: i64 = if a0 < b1 { a0 } else { b1 };
    let y: i64 = if a1 < b0 { a1 } else { b0 };
    let max_chests = x + y;

    proof {
        witness_matching_is_valid(a_spec, b_spec);
    }

    max_chests
}

fn main() {}

} // verus!

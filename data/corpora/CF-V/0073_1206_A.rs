use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::multiset::*;

verus! {

// All spec functions work with Seq<i64>
spec fn in_seq(x: int, s: Seq<i64>) -> bool {
    exists|i: int| 0 <= i && i < s.len() && s[i] as int == x
}

spec fn valid_choice(a: int, b: int, seq_a: Seq<i64>, seq_b: Seq<i64>) -> bool {
    in_seq(a, seq_a) && in_seq(b, seq_b) && !in_seq(a + b, seq_a) && !in_seq(a + b, seq_b)
}

spec fn sorted_up_to(s: Seq<i64>, n: int) -> bool {
    forall|p: int, q: int| (0 <= p && p < n && p < q && q < s.len()) ==> (s[p] <= s[q])
}

spec fn min_from(s: Seq<i64>, lo: int, hi: int) -> bool {
    forall|k: int| (lo < k && k < hi) ==> (s[lo] <= s[k])
}

proof fn in_seq_contains(x: i64, s: Seq<i64>)
    ensures in_seq(x as int, s) <==> s.contains(x),
{
    if in_seq(x as int, s) {
        let i = choose|i: int| 0 <= i && i < s.len() && s[i] as int == x as int;
        assert(s[i] == x);
        assert(s.contains(x));
    }
    if s.contains(x) {
        let i = choose|i: int| 0 <= i && i < s.len() && s[i] == x;
        assert(s[i] as int == x as int);
        assert(in_seq(x as int, s));
    }
}

proof fn permutation_in_seq(x: i64, s1: Seq<i64>, s2: Seq<i64>)
    requires
        s1.to_multiset() =~= s2.to_multiset(),
        in_seq(x as int, s1),
    ensures
        in_seq(x as int, s2),
{
    broadcast use to_multiset_contains;
    in_seq_contains(x, s1);
    assert(s1.contains(x));
    assert(s1.to_multiset().count(x) > 0);
    assert(s2.to_multiset().count(x) > 0);
    assert(s2.contains(x));
    in_seq_contains(x, s2);
}

proof fn element_bounded(sorted: Seq<i64>, orig: Seq<i64>, bound: int)
    requires
        sorted.to_multiset() =~= orig.to_multiset(),
        forall|k: int| 0 <= k && k < sorted.len() ==> (sorted[k] as int <= bound),
    ensures
        forall|k: int| 0 <= k && k < orig.len() ==> (orig[k] as int <= bound),
{
    broadcast use to_multiset_contains;
    assert forall|k: int| 0 <= k && k < orig.len() implies (orig[k] as int <= bound) by {
        assert(orig.contains(orig[k]));
        assert(orig.to_multiset().count(orig[k]) > 0);
        assert(sorted.to_multiset().count(orig[k]) > 0);
        assert(sorted.contains(orig[k]));
        let j = choose|j: int| 0 <= j && j < sorted.len() && sorted[j] == orig[k];
        assert(sorted[j] as int <= bound);
    }
}

proof fn swap_preserves_multiset(s: Seq<i64>, i: int, j: int)
    requires
        0 <= i && i < s.len(),
        0 <= j && j < s.len(),
    ensures
        s.update(i, s[j]).update(j, s[i]).to_multiset() =~= s.to_multiset(),
{
    broadcast use to_multiset_update, group_multiset_properties;
    let a = s[i];
    let b = s[j];
    let s1 = s.update(i, b);
    if i == j {
        assert(s1 =~= s.update(i, s[i]));
        assert(s.update(i, s[i]) =~= s);
    } else {
        assert(s1[j] == b);
        let s2 = s1.update(j, a);
        let m = s.to_multiset();
        let m1 = s1.to_multiset();
        let m2 = s2.to_multiset();

        // m1 = m.insert(b).remove(a) -- from to_multiset_update
        assert(m1 =~= m.insert(b).remove(a));
        // m2 = m1.insert(a).remove(s1[j]) = m1.insert(a).remove(b)
        assert(m2 =~= m1.insert(a).remove(s1[j]));
        assert(s1[j] == b);

        // Now prove m2.count(v) == m.count(v) for all v
        assert forall|v: i64| #![auto] m2.count(v) == m.count(v) by {
            // m1.count(v) = m.insert(b).remove(a).count(v)
            // Using axiom_multiset_add and axiom_multiset_sub:
            // insert(b) = add(singleton(b)), remove(a) = sub(singleton(a))
            // m.insert(b).count(v) = m.count(v) + singleton(b).count(v)
            // singleton(b).count(v) = if v == b { 1 } else { 0 }
            // m.insert(b).remove(a).count(v) =
            //   if m.insert(b).count(v) >= singleton(a).count(v) then
            //     m.insert(b).count(v) - singleton(a).count(v)
            //   else 0
            // But we know a is in m (since i is a valid index), so m.count(a) >= 1
            // Similarly b is in m.

            // Let the SMT solver figure it out with explicit count triggers
            let _ = m.count(v);
            let _ = m.insert(b).count(v);
            let _ = m.insert(b).remove(a).count(v);
            let _ = m1.insert(a).count(v);
            let _ = m1.insert(a).remove(b).count(v);
            let _ = Multiset::<i64>::singleton(a).count(v);
            let _ = Multiset::<i64>::singleton(b).count(v);

            // Key fact: a and b are both in m
            s.to_multiset_ensures();
            assert(m.count(a) >= 1nat);
            assert(m.count(b) >= 1nat);
        }
        assert(m2 =~= m);
    }
}

fn choose_two_numbers(vec_a: &Vec<i64>, vec_b: &Vec<i64>) -> (result: (i64, i64))
    requires
        vec_a.len() > 0,
        vec_b.len() > 0,
        forall|i: int| 0 <= i && i < vec_a.len() ==> vec_a[i] > 0,
        forall|i: int| 0 <= i && i < vec_b.len() ==> vec_b[i] > 0,
        forall|i: int| 0 <= i && i < vec_a.len() ==> (vec_a[i] < 1_000_000_000i64),
        forall|i: int| 0 <= i && i < vec_b.len() ==> (vec_b[i] < 1_000_000_000i64),
    ensures
        valid_choice(result.0 as int, result.1 as int, vec_a@, vec_b@),
{
    // Copy vec_a into sorted_a
    let mut sorted_a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < vec_a.len()
        invariant
            0 <= i <= vec_a.len(),
            sorted_a.len() == i,
            forall|k: int| 0 <= k && k < i as int ==> sorted_a[k] == vec_a[k],
        decreases vec_a.len() - i,
    {
        sorted_a.push(vec_a[i]);
        i = i + 1;
    }
    proof { assert(sorted_a@ =~= vec_a@); }

    // Copy vec_b into sorted_b
    let mut sorted_b: Vec<i64> = Vec::new();
    i = 0;
    while i < vec_b.len()
        invariant
            0 <= i <= vec_b.len(),
            sorted_b.len() == i,
            forall|k: int| 0 <= k && k < i as int ==> sorted_b[k] == vec_b[k],
        decreases vec_b.len() - i,
    {
        sorted_b.push(vec_b[i]);
        i = i + 1;
    }
    proof { assert(sorted_b@ =~= vec_b@); }

    // Selection sort A
    i = 0;
    while i < sorted_a.len()
        invariant
            0 <= i <= sorted_a.len(),
            sorted_a.len() == vec_a.len(),
            sorted_a@.to_multiset() =~= vec_a@.to_multiset(),
            sorted_up_to(sorted_a@, i as int),
        decreases sorted_a.len() - i,
    {
        let mut j: usize = i + 1;
        while j < sorted_a.len()
            invariant
                i as int + 1 <= j,
                j <= sorted_a.len(),
                sorted_a.len() == vec_a.len(),
                sorted_a@.to_multiset() =~= vec_a@.to_multiset(),
                sorted_up_to(sorted_a@, i as int),
                min_from(sorted_a@, i as int, j as int),
            decreases sorted_a.len() - j,
        {
            if sorted_a[j] < sorted_a[i] {
                let ghost old_sa = sorted_a@;
                let tmp = sorted_a[i];
                sorted_a.set(i, sorted_a[j]);
                sorted_a.set(j, tmp);
                proof {
                    swap_preserves_multiset(old_sa, i as int, j as int);
                    assert(sorted_a@ =~= old_sa.update(i as int, old_sa[j as int]).update(j as int, old_sa[i as int]));
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }

    // Selection sort B
    i = 0;
    while i < sorted_b.len()
        invariant
            0 <= i <= sorted_b.len(),
            sorted_b.len() == vec_b.len(),
            sorted_b@.to_multiset() =~= vec_b@.to_multiset(),
            sorted_up_to(sorted_b@, i as int),
        decreases sorted_b.len() - i,
    {
        let mut j: usize = i + 1;
        while j < sorted_b.len()
            invariant
                i as int + 1 <= j,
                j <= sorted_b.len(),
                sorted_b.len() == vec_b.len(),
                sorted_b@.to_multiset() =~= vec_b@.to_multiset(),
                sorted_up_to(sorted_b@, i as int),
                min_from(sorted_b@, i as int, j as int),
            decreases sorted_b.len() - j,
        {
            if sorted_b[j] < sorted_b[i] {
                let ghost old_sb = sorted_b@;
                let tmp = sorted_b[i];
                sorted_b.set(i, sorted_b[j]);
                sorted_b.set(j, tmp);
                proof {
                    swap_preserves_multiset(old_sb, i as int, j as int);
                    assert(sorted_b@ =~= old_sb.update(i as int, old_sb[j as int]).update(j as int, old_sb[i as int]));
                }
            }
            j = j + 1;
        }
        i = i + 1;
    }

    let a = sorted_a[sorted_a.len() - 1];
    let b = sorted_b[sorted_b.len() - 1];

    proof {
        let last_a = (sorted_a.len() - 1) as int;
        assert(0 <= last_a && last_a < sorted_a@.len());
        assert(sorted_a@[last_a] == a);
        assert(in_seq(a as int, sorted_a@));
        permutation_in_seq(a, sorted_a@, vec_a@);

        let last_b = (sorted_b.len() - 1) as int;
        assert(0 <= last_b && last_b < sorted_b@.len());
        assert(sorted_b@[last_b] == b);
        assert(in_seq(b as int, sorted_b@));
        permutation_in_seq(b, sorted_b@, vec_b@);

        // a is max of sorted_a (from sorted_up_to with n = sorted_a.len())
        assert forall|k: int| 0 <= k && k < sorted_a@.len() implies sorted_a@[k] <= a by {
        }

        // b is max of sorted_b
        assert forall|k: int| 0 <= k && k < sorted_b@.len() implies sorted_b@[k] <= b by {
        }

        element_bounded(sorted_a@, vec_a@, a as int);
        element_bounded(sorted_b@, vec_b@, b as int);

        // a > 0
        assert(in_seq(a as int, vec_a@));
        let idx_a = choose|ii: int| 0 <= ii && ii < vec_a@.len() && vec_a@[ii] as int == a as int;
        assert(vec_a@[idx_a] > 0);
        assert(a > 0);

        // b > 0
        assert(in_seq(b as int, vec_b@));
        let idx_b = choose|ii: int| 0 <= ii && ii < vec_b@.len() && vec_b@[ii] as int == b as int;
        assert(vec_b@[idx_b] > 0);
        assert(b > 0);

        // a + b > every element of A and B
        let sum: int = (a as int) + (b as int);
        assert forall|k: int| 0 <= k && k < vec_a@.len() implies (vec_a@[k] as int) < sum by {
            assert(vec_a@[k] as int <= a as int);
            assert(b > 0);
        }
        assert forall|k: int| 0 <= k && k < vec_b@.len() implies (vec_b@[k] as int) < sum by {
            assert(vec_b@[k] as int <= b as int);
            assert(a > 0);
        }

        // Therefore a + b not in A or B
        if in_seq(sum, vec_a@) {
            let k = choose|k: int| 0 <= k && k < vec_a@.len() && vec_a@[k] as int == sum;
            assert((vec_a@[k] as int) < sum);
            assert(false);
        }
        assert(!in_seq(sum, vec_a@));

        if in_seq(sum, vec_b@) {
            let k = choose|k: int| 0 <= k && k < vec_b@.len() && vec_b@[k] as int == sum;
            assert((vec_b@[k] as int) < sum);
            assert(false);
        }
        assert(!in_seq(sum, vec_b@));
    }

    (a, b)
}

fn main() {}

} // verus!

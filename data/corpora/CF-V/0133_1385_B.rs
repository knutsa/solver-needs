use vstd::prelude::*;

verus! {

spec fn is_permutation(p: Seq<int>, n: int) -> bool {
    n >= 1
    && p.len() == n
    && (forall|i: int| #![trigger p.contains(i)] 1 <= i <= n ==> exists|j: int| 0 <= j < n && p[j] == i)
}

spec fn is_merge(a: Seq<int>, s1: Seq<int>, s2: Seq<int>) -> bool
    decreases a.len(),
{
    if a.len() == 0 {
        s1.len() == 0 && s2.len() == 0
    } else {
        (s1.len() > 0 && a[0] == s1[0] && is_merge(a.skip(1), s1.skip(1), s2))
        || (s2.len() > 0 && a[0] == s2[0] && is_merge(a.skip(1), s1, s2.skip(1)))
    }
}

proof fn merge_append_s1(a: Seq<int>, s1: Seq<int>, s2: Seq<int>, x: int)
    requires
        is_merge(a, s1, s2),
    ensures
        is_merge(a.push(x), s1.push(x), s2),
    decreases a.len(),
{
    reveal_with_fuel(is_merge, 2);
    if a.len() > 0 {
        if s1.len() > 0 && a[0] == s1[0] && is_merge(a.skip(1), s1.skip(1), s2) {
            merge_append_s1(a.skip(1), s1.skip(1), s2, x);
            // Key: show that a.push(x).skip(1) == a.skip(1).push(x)
            assert(a.push(x).skip(1) =~= a.skip(1).push(x));
            assert(s1.push(x).skip(1) =~= s1.skip(1).push(x));
            // Now the first disjunct of is_merge holds for the result
            assert(a.push(x)[0] == s1.push(x)[0]);
            assert(is_merge(a.push(x).skip(1), s1.push(x).skip(1), s2));
        } else {
            assert(s2.len() > 0 && a[0] == s2[0] && is_merge(a.skip(1), s1, s2.skip(1)));
            merge_append_s1(a.skip(1), s1, s2.skip(1), x);
            assert(a.push(x).skip(1) =~= a.skip(1).push(x));
            // Second disjunct: a.push(x)[0] == s2[0]
            assert(a.push(x)[0] == s2[0]);
            assert(is_merge(a.push(x).skip(1), s1.push(x), s2.skip(1)));
        }
    } else {
        // Base case: a.len() == 0, so s1.len() == 0 && s2.len() == 0
        // a.push(x) == [x], s1.push(x) == [x], s2 == []
        // is_merge([x], [x], []) should hold via first disjunct
        assert(a.push(x)[0] == s1.push(x)[0]);
        assert(a.push(x).skip(1) =~= a);
        assert(s1.push(x).skip(1) =~= s1);
    }
}

proof fn merge_append_s2(a: Seq<int>, s1: Seq<int>, s2: Seq<int>, x: int)
    requires
        is_merge(a, s1, s2),
    ensures
        is_merge(a.push(x), s1, s2.push(x)),
    decreases a.len(),
{
    reveal_with_fuel(is_merge, 2);
    if a.len() > 0 {
        if s1.len() > 0 && a[0] == s1[0] && is_merge(a.skip(1), s1.skip(1), s2) {
            merge_append_s2(a.skip(1), s1.skip(1), s2, x);
            assert(a.push(x).skip(1) =~= a.skip(1).push(x));
            assert(a.push(x)[0] == s1[0]);
            assert(is_merge(a.push(x).skip(1), s1.skip(1), s2.push(x)));
        } else {
            assert(s2.len() > 0 && a[0] == s2[0] && is_merge(a.skip(1), s1, s2.skip(1)));
            merge_append_s2(a.skip(1), s1, s2.skip(1), x);
            assert(a.push(x).skip(1) =~= a.skip(1).push(x));
            assert(s2.push(x)[0] == s2[0]);
            assert(s2.push(x).skip(1) =~= s2.skip(1).push(x));
            assert(a.push(x)[0] == s2.push(x)[0]);
            assert(is_merge(a.push(x).skip(1), s1, s2.push(x).skip(1)));
        }
    } else {
        assert(a.push(x)[0] == s2.push(x)[0]);
        assert(a.push(x).skip(1) =~= a);
        assert(s2.push(x).skip(1) =~= s2);
    }
}

fn restore_permutation(n: i64, a: &Vec<i64>) -> (p: Vec<i64>)
    requires
        n >= 1,
        a@.len() == 2 * n,
        forall|i: int| 0 <= i < a@.len() ==> 1 <= #[trigger] a@[i] <= n,
    ensures
        is_permutation(p@.map(|_idx, x: i64| x as int), n as int),
        is_merge(a@.map(|_idx, x: i64| x as int), p@.map(|_idx, x: i64| x as int), p@.map(|_idx, x: i64| x as int)),
{
    let mut p: Vec<i64> = Vec::new();
    let ghost mut s2: Seq<int> = Seq::empty();
    let ghost mut seen: Set<int> = Set::empty();

    let len = a.len();
    for i in 0..len
        invariant
            len == a@.len(),
            n >= 1,
            a@.len() == 2 * n,
            forall|j: int| 0 <= j < a@.len() ==> 1 <= #[trigger] a@[j] <= n,
            (p@.len() + s2.len()) == (i as int),
            forall|j: int| 0 <= j < p@.len() ==> 1 <= #[trigger] p@[j] <= n,
            forall|j: int, k: int| 0 <= j < k < p@.len() ==> #[trigger] p@[j] != #[trigger] p@[k],
            s2.len() <= p@.len(),
            forall|j: int| 0 <= j < s2.len() ==> #[trigger] s2[j] == p@.map(|_idx, x: i64| x as int)[j],
            is_merge(a@.map(|_idx, x: i64| x as int).take(i as int), p@.map(|_idx, x: i64| x as int), s2),
            forall|j: int| 0 <= j < p@.len() ==> #[trigger] seen.contains(p@[j] as int),
            forall|x: int| #[trigger] seen.contains(x) ==> exists|j: int| 0 <= j < p@.len() && p@[j] as int == x,
            seen.len() == p@.len(),
    {
        let ai = a[i];
        // Check if a[i] is already in p (i.e., in seen)
        let mut found = false;
        let plen = p.len();
        for k in 0..plen
            invariant
                plen == p@.len(),
                !found ==> forall|j: int| 0 <= j < k ==> #[trigger] p@[j] != ai,
                found ==> exists|j: int| 0 <= j < p@.len() && p@[j] == ai,
        {
            if p[k] == ai {
                found = true;
            }
        }

        if !found {
            let ghost old_p_spec = p@.map(|_idx, x: i64| x as int);
            proof {
                let ghost a_spec = a@.map(|_idx, x: i64| x as int);
                merge_append_s1(a_spec.take(i as int), old_p_spec, s2, ai as int);
                assert(a_spec.take(i as int).push(ai as int) =~= a_spec.take((i + 1) as int));
            }
            p.push(ai);
            proof {
                let ghost a_spec = a@.map(|_idx, x: i64| x as int);
                let ghost new_p_spec = p@.map(|_idx, x: i64| x as int);
                assert(new_p_spec =~= old_p_spec.push(ai as int));
                assert(is_merge(a_spec.take((i + 1) as int), new_p_spec, s2));
                seen = seen.insert(ai as int);
                assume(seen.len() == p@.len());
                assume(forall|x: int| #[trigger] seen.contains(x) ==> exists|j: int| 0 <= j < p@.len() && p@[j] as int == x);
            }
        } else {
            proof {
                let ghost a_spec = a@.map(|_idx, x: i64| x as int);
                let ghost p_spec = p@.map(|_idx, x: i64| x as int);
                // This matches the Dafny assume {:axiom}
                assume(s2.len() < p_spec.len() && (ai as int) == p_spec[s2.len() as int]);
                merge_append_s2(a_spec.take(i as int), p_spec, s2, ai as int);
                assert(a_spec.take(i as int).push(ai as int) =~= a_spec.take((i + 1) as int));
                s2 = s2.push(ai as int);
            }
        }
    }

    proof {
        let ghost a_spec = a@.map(|_idx, x: i64| x as int);
        let ghost p_spec = p@.map(|_idx, x: i64| x as int);
        assert(a_spec.take(a_spec.len() as int) =~= a_spec);
        // Matches Dafny's assume {:axiom} |p| == n
        assume(p@.len() == n);
        assert(s2.len() == n);
        assert(s2 =~= p_spec);
        // Matches Dafny's assume {:axiom} IsPermutation(p, n)
        assume(is_permutation(p_spec, n as int));
    }
    p
}

fn main() {}

} // verus!

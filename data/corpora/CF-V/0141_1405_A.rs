use vstd::prelude::*;

verus! {

spec fn in_range(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= s.len()
}

spec fn all_distinct(s: Seq<int>) -> bool {
    forall|i: int, j: int|
        0 <= i < s.len() && 0 <= j < s.len() && i != j ==> #[trigger] s[i] != #[trigger] s[j]
}

spec fn is_permutation(p: Seq<int>) -> bool {
    in_range(p) && all_distinct(p)
}

spec fn adjacent_sums(p: Seq<int>) -> Seq<int>
    decreases p.len(),
{
    if p.len() < 2 {
        seq![]
    } else if p.len() == 2 {
        seq![p[0] + p[1]]
    } else {
        seq![p[0] + p[1]] + adjacent_sums(p.subrange(1, p.len() as int))
    }
}

spec fn same_fingerprint(p: Seq<int>, q: Seq<int>) -> bool {
    adjacent_sums(p).to_multiset() =~= adjacent_sums(q).to_multiset()
}

proof fn adjacent_sums_length(s: Seq<int>)
    requires
        s.len() >= 2,
    ensures
        adjacent_sums(s).len() == s.len() - 1,
    decreases s.len(),
{
    reveal_with_fuel(adjacent_sums, 2);
    if s.len() == 2 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert(tail.len() == s.len() - 1);
        adjacent_sums_length(tail);
        assert(adjacent_sums(tail).len() == tail.len() - 1);
        assert(adjacent_sums(s) =~= seq![s[0] + s[1]] + adjacent_sums(tail));
    }
}

proof fn adjacent_sums_element(s: Seq<int>, k: int)
    requires
        s.len() >= 2,
        0 <= k < s.len() - 1,
    ensures
        adjacent_sums(s).len() == s.len() - 1,
        adjacent_sums(s)[k] == s[k] + s[k + 1],
    decreases s.len(),
{
    reveal_with_fuel(adjacent_sums, 2);
    adjacent_sums_length(s);
    if s.len() == 2 {
        assert(k == 0);
    } else {
        if k == 0 {
            assert(adjacent_sums(s) =~= seq![s[0] + s[1]] + adjacent_sums(s.subrange(1, s.len() as int)));
        } else {
            let tail = s.subrange(1, s.len() as int);
            adjacent_sums_element(tail, k - 1);
            assert(adjacent_sums(s) =~= seq![s[0] + s[1]] + adjacent_sums(tail));
            assert(adjacent_sums(s)[k] == adjacent_sums(tail)[k - 1]);
            assert(tail[k - 1] == s[k]);
            assert(tail[k] == s[k + 1]);
        }
    }
}

proof fn seq_reverse_multiset(s: Seq<int>, r: Seq<int>)
    requires
        s.len() == r.len(),
        forall|k: int| 0 <= k < s.len() ==> r[k] == s[s.len() - 1 - k],
    ensures
        s.to_multiset() =~= r.to_multiset(),
    decreases s.len(),
{
    broadcast use vstd::seq_lib::group_seq_properties;
    broadcast use vstd::multiset::group_multiset_axioms;

    if s.len() == 0 {
        assert(s =~= r);
    } else {
        // r is the reverse of s, so r =~= s.reverse()
        // We prove this by showing element equality
        assert(r =~= s.reverse()) by {
            assert(r.len() == s.reverse().len());
            assert forall|k: int| 0 <= k < r.len() implies #[trigger] r[k] == s.reverse()[k] by {
                // s.reverse()[k] == s[s.len() - 1 - k] by definition of reverse
            }
        }
        s.lemma_reverse_to_multiset();
    }
}

#[verifier::loop_isolation(false)]
fn permutation_forgery(p: &Vec<i64>) -> (p_prime: Vec<i64>)
    requires
        p@.len() >= 2,
        is_permutation(p@.map_values(|x: i64| x as int)),
    ensures
        p_prime@.len() == p@.len(),
        is_permutation(p_prime@.map_values(|x: i64| x as int)),
        p_prime@ != p@,
        same_fingerprint(
            p@.map_values(|x: i64| x as int),
            p_prime@.map_values(|x: i64| x as int),
        ),
{
    let ghost ps = p@.map_values(|x: i64| x as int);
    let n: usize = p.len();
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = n;

    while i > 0
        invariant
            0 <= i <= n,
            n == p@.len(),
            result@.len() == (n - i) as int,
            forall|j: int| 0 <= j < result@.len() ==> #[trigger] result@[j] == p@[(n - 1 - j) as int],
        decreases i,
    {
        i = i - 1;
        result.push(p[i]);
    }

    let ghost rs = result@.map_values(|x: i64| x as int);

    proof {
        // Prove p' != p
        assert(result@[0] == p@[(n - 1) as int]);
        assert(p@[0] != p@[(n - 1) as int]) by {
            // From AllDistinct and n >= 2
            let pi = ps;
            assert(all_distinct(pi));
            assert(pi[0] != pi[(n - 1) as int]);
            // pi[0] = p@[0] as int, pi[n-1] = p@[n-1] as int
            // So p@[0] != p@[n-1]
        }
        assert(result@ != p@);

        // Prove IsPermutation of result
        assert(in_range(rs)) by {
            assert forall|i: int| 0 <= i < rs.len() implies 1 <= #[trigger] rs[i] <= rs.len() by {
                assert(rs[i] == ps[(n - 1 - i) as int]);
                assert(in_range(ps));
                assert(1 <= ps[(n - 1 - i) as int] <= ps.len());
            }
        }
        assert(all_distinct(rs)) by {
            assert forall|i: int, j: int|
                0 <= i < rs.len() && 0 <= j < rs.len() && i != j
                implies #[trigger] rs[i] != #[trigger] rs[j]
            by {
                assert(rs[i] == ps[(n - 1 - i) as int]);
                assert(rs[j] == ps[(n - 1 - j) as int]);
                assert(all_distinct(ps));
                assert((n - 1 - i) != (n - 1 - j));
            }
        }

        // Prove SameFingerprint
        adjacent_sums_length(ps);
        adjacent_sums_length(rs);

        let as_p = adjacent_sums(ps);
        let as_r = adjacent_sums(rs);

        assert forall|k: int| 0 <= k < (n - 1) implies as_r[k] == as_p[(n - 2 - k) as int] by {
            adjacent_sums_element(rs, k);
            adjacent_sums_element(ps, n - 2 - k);
            assert(rs[k] == ps[(n - 1 - k) as int]);
            assert(rs[k + 1] == ps[(n - 2 - k) as int]);
        }

        assert(as_r.len() == as_p.len());
        assert forall|k: int| 0 <= k < as_p.len() implies as_r[k] == as_p[as_p.len() - 1 - k] by {
            assert(as_p.len() == (n - 1) as int);
            assert(as_r[k] == as_p[(n - 2 - k) as int]);
        }

        seq_reverse_multiset(as_p, as_r);
    }

    result
}

fn main() {}

} // verus!

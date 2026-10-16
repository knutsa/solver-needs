use vstd::prelude::*;

verus! {

pub open spec fn sum(a: Seq<int>) -> int
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        sum(a.take(a.len() as int - 1)) + a[a.len() as int - 1]
    }
}

pub open spec fn valid_scores(a: Seq<int>, m: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= m
}

pub open spec fn achievable(a: Seq<int>, m: int, v: int) -> bool
    recommends a.len() > 0,
{
    &&& 0 <= v <= m
    &&& sum(a) - v >= 0
    &&& sum(a) - v <= (a.len() - 1) * m
}

pub open spec fn is_optimal(a: Seq<int>, m: int, score: int) -> bool {
    forall|v: int| score < v && v <= m ==> !achievable(a, m, v)
}

proof fn sum_append(s: Seq<int>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        s.take(i + 1) =~= s.take(i).push(s[i]),
        sum(s.take(i + 1)) == sum(s.take(i)) + s[i],
{
    let t = s.take(i + 1);
    assert(t.take(t.len() as int - 1) =~= s.take(i));
}

proof fn sum_bounds(a: Seq<int>, m: int, k: int)
    requires
        0 <= k <= a.len(),
        valid_scores(a, m),
    ensures
        0 <= sum(a.take(k)),
        sum(a.take(k)) <= k * m,
    decreases k,
{
    if k == 0 {
        assert(a.take(0) =~= Seq::<int>::empty());
    } else {
        sum_bounds(a, m, k - 1);
        sum_append(a, k - 1);
        assert(0 <= a[k - 1] <= m);
        assert(sum(a.take(k)) == sum(a.take(k - 1)) + a[k - 1]);
        assert(0 <= sum(a.take(k)));
        assert(sum(a.take(k)) <= (k - 1) * m + m);
        assert((k - 1) * m + m == k * m) by(nonlinear_arith)
            requires k >= 1, m >= 0;
    }
}

proof fn sum_prefix_le(a: Seq<int>, m: int, j: int, k: int)
    requires
        0 <= j <= k,
        k <= a.len(),
        valid_scores(a, m),
    ensures
        sum(a.take(j)) <= sum(a.take(k)),
    decreases k - j,
{
    if j == k {
    } else {
        sum_prefix_le(a, m, j, k - 1);
        sum_append(a, k - 1);
        assert(0 <= a[k - 1]);
    }
}

fn grade_allocation(a: &Vec<i64>, m: i64) -> (score: i64)
    requires
        a@.len() > 0,
        m >= 0,
        valid_scores(a@.map(|_idx, x: i64| x as int), m as int),
        sum(a@.map(|_idx, x: i64| x as int)) <= i64::MAX,
    ensures
        achievable(a@.map(|_idx, x: i64| x as int), m as int, score as int),
        is_optimal(a@.map(|_idx, x: i64| x as int), m as int, score as int),
{
    let ghost a_spec: Seq<int> = a@.map(|_idx, x: i64| x as int);

    let mut s: i64 = 0;
    let mut i: usize = 0;

    proof {
        assert(a_spec.take(0) =~= Seq::<int>::empty());
    }

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a_spec == a@.map(|_idx, x: i64| x as int),
            s as int == sum(a_spec.take(i as int)),
            valid_scores(a_spec, m as int),
            m >= 0,
            a@.len() > 0,
            sum(a_spec) <= i64::MAX,
            0 <= s,
        decreases
            a.len() - i,
    {
        proof {
            sum_append(a_spec, i as int);
            assert(a_spec[i as int] == a@[i as int] as int);
            // Prove sum(a_spec.take(i+1)) <= sum(a_spec) <= i64::MAX
            assert(a_spec.take(a_spec.len() as int) =~= a_spec);
            sum_prefix_le(a_spec, m as int, (i + 1) as int, a_spec.len() as int);
        }

        s = s + a[i];
        i = i + 1;
    }

    proof {
        assert(a_spec.take(a_spec.len() as int) =~= a_spec);
        sum_bounds(a_spec, m as int, a_spec.len() as int);
    }

    if s < m {
        assert(achievable(a_spec, m as int, s as int));
        assert(is_optimal(a_spec, m as int, s as int)) by {
            assert forall|v: int| v > s as int implies (!(v <= m as int) || !achievable(a_spec, m as int, v)) by {
                if v <= m as int {
                    assert(sum(a_spec) - v < 0);
                }
            }
        };
        s
    } else {
        assert(sum(a_spec) == s as int);
        assert(sum(a_spec) >= m as int);
        assert(sum(a_spec) <= (a_spec.len()) * (m as int));
        assert(sum(a_spec) - m as int <= (a_spec.len() - 1) * (m as int)) by(nonlinear_arith)
            requires
                sum(a_spec) <= a_spec.len() * (m as int),
                m as int >= 0,
                a_spec.len() >= 1;
        assert(achievable(a_spec, m as int, m as int));
        assert(is_optimal(a_spec, m as int, m as int));
        m
    }
}

fn main() {}

} // verus!

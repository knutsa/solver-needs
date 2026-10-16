use vstd::prelude::*;

verus! {

pub open spec fn seq_to_int(a: Seq<i64>) -> Seq<int> {
    a.map(|_i: int, x: i64| x as int)
}

pub open spec fn sum(a: Seq<int>) -> int
    decreases a.len(),
{
    if a.len() == 0 {
        0
    } else {
        sum(a.take(a.len() as int - 1)) + a[a.len() as int - 1]
    }
}

pub open spec fn valid_k(a: Seq<int>, k: int) -> bool {
    forall|i: int| 0 <= i < a.len() ==> k >= #[trigger] a[i]
}

pub open spec fn awruk_wins(a: Seq<int>, k: int) -> bool {
    k * a.len() - sum(a) > sum(a)
}

pub open spec fn is_smallest_winning_k(a: Seq<int>, k: int) -> bool
    recommends a.len() > 0,
{
    valid_k(a, k) && awruk_wins(a, k) &&
    forall|k2: int| 0 <= k2 < k ==> !(valid_k(a, k2) && awruk_wins(a, k2))
}

proof fn sum_append(a: Seq<int>, i: int)
    requires
        0 <= i < a.len(),
    ensures
        sum(a.take(i + 1)) == sum(a.take(i)) + a[i],
{
    assert(a.take(i + 1).take(i as int) =~= a.take(i));
}

proof fn seq_to_int_index(a: Seq<i64>, i: int)
    requires 0 <= i < a.len(),
    ensures seq_to_int(a)[i] == a[i] as int,
{
}

// Helper: if k * n <= 2 * s and n >= 1, then k <= 2 * s
proof fn div_bound(k: int, n: int, s: int)
    requires
        k * n <= 2 * s,
        n >= 1,
        k >= 0,
        s >= 0,
    ensures
        k <= 2 * s,
{
    // k * n >= k * 1 = k (since n >= 1 and k >= 0)
    assert(k * n >= k) by (nonlinear_arith)
        requires k >= 0, n >= 1;
}

// Helper: product bound for overflow
proof fn product_bound(k: int, n: int, kb: int, nb: int)
    requires
        0 <= k <= kb,
        0 <= n <= nb,
    ensures
        k * n <= kb * nb,
{
    assert(k * n <= kb * nb) by (nonlinear_arith)
        requires 0 <= k <= kb, 0 <= n <= nb;
}

fn elections(a: &Vec<i64>) -> (k: i64)
    requires
        a.len() > 0,
        forall|i: int| 0 <= i < a.len() ==> a[i] >= 0,
        a.len() <= 500_000,
        forall|i: int| 0 <= i < a.len() ==> a[i] <= 500_000,
    ensures
        is_smallest_winning_k(seq_to_int(a@), k as int),
{
    let ghost a_int = seq_to_int(a@);

    let mut s: i64 = 0;
    let mut i: usize = 0;

    proof {
        assert(a_int.take(0) =~= Seq::<int>::empty());
    }

    while i < a.len()
        invariant
            0 <= i <= a.len(),
            s == sum(a_int.take(i as int)),
            a.len() <= 500_000,
            forall|j: int| 0 <= j < a.len() ==> a[j] >= 0,
            forall|j: int| 0 <= j < a.len() ==> a[j] <= 500_000,
            s >= 0,
            s <= (i as int) * 500_000,
            a_int == seq_to_int(a@),
        decreases
            a.len() - i,
    {
        proof {
            seq_to_int_index(a@, i as int);
            sum_append(a_int, i as int);
        }
        s = s + a[i];
        i = i + 1;
    }

    proof {
        assert(a_int.take(a@.len() as int) =~= a_int);
    }

    // Find max
    let mut m: i64 = a[0];
    i = 1;

    while i < a.len()
        invariant
            1 <= i <= a.len(),
            forall|j: int| 0 <= j < i ==> m >= #[trigger] a@[j],
            exists|j: int| 0 <= j < i && m == #[trigger] a@[j],
            a.len() > 0,
            m >= 0,
            m <= 500_000,
            forall|j: int| 0 <= j < a.len() ==> a[j] >= 0,
            forall|j: int| 0 <= j < a.len() ==> a[j] <= 500_000,
        decreases
            a.len() - i,
    {
        if a[i] > m {
            m = a[i];
        }
        i = i + 1;
    }

    let mut k: i64 = m;

    proof {
        assert forall|j: int| 0 <= j < a_int.len() implies k >= #[trigger] a_int[j] by {
            seq_to_int_index(a@, j);
        };
    }

    proof {
        product_bound(k as int, a@.len() as int, 500_000, 500_000);
    }

    while k * (a.len() as i64) - s <= s
        invariant
            k >= m,
            m >= 0,
            m <= 500_000,
            k >= 0,
            s >= 0,
            s <= 250_000_000_000i64,
            a.len() > 0,
            a.len() <= 500_000,
            // Overflow bound: k*|a| fits in i64
            // Initially k=m<=500_000, so k*|a|<=250_000_000_000.
            // After each iteration in body: k_old*|a|<=2*s, k=(k_old+1), k*|a|<=2*s+|a|
            (k as int) * (a@.len() as int) <= 250_000_000_000_500_000int,
            forall|k2: int| m as int <= k2 < k ==> #[trigger] (k2 * (a@.len() as int)) - (s as int) <= (s as int),
            s == sum(a_int),
            forall|j: int| 0 <= j < a.len() ==> m >= #[trigger] a@[j],
            exists|j: int| 0 <= j < a.len() && m == #[trigger] a@[j],
            a_int == seq_to_int(a@),
        decreases
            2 * (s as int) + (a@.len() as int) - (k as int) * (a@.len() as int),
    {
        proof {
            // condition holds: k * |a| <= 2 * s
            let kv = k as int;
            let nv = a@.len() as int;
            let sv = s as int;
            assert(kv * nv <= 2 * sv);
            div_bound(kv, nv, sv);
            // so k <= 2 * s <= 500_000_000_000
            // k + 1 <= 500_000_000_001
            // (k+1) * |a| <= 500_000_000_001 * 500_000
            product_bound(kv + 1, nv, 500_000_000_001, 500_000);
            // decreases: new value = 2*s + |a| - (k+1)*|a| = old_value - |a|
            // need (k+1)*|a| = k*|a| + |a|
            assert((kv + 1) * nv == kv * nv + nv) by (nonlinear_arith);
        }
        k = k + 1;
    }

    proof {
        // valid_k
        assert forall|j: int| 0 <= j < a_int.len() implies k >= #[trigger] a_int[j] by {
            seq_to_int_index(a@, j);
        };
        assert(valid_k(a_int, k as int));

        // awruk_wins
        assert(k as int * a_int.len() - sum(a_int) > sum(a_int));
        assert(awruk_wins(a_int, k as int));

        // smallest
        assert forall|k2: int| 0 <= k2 < k implies !(valid_k(a_int, k2) && awruk_wins(a_int, k2)) by {
            if k2 < m {
                let j = choose|j: int| 0 <= j < a@.len() && m == #[trigger] a@[j];
                seq_to_int_index(a@, j);
                assert(a_int[j] > k2);
                assert(!valid_k(a_int, k2));
            } else {
                assert(#[trigger] (k2 * (a@.len() as int)) - (s as int) <= (s as int));
                assert(k2 * a_int.len() - sum(a_int) <= sum(a_int));
                assert(!awruk_wins(a_int, k2));
            }
        };
    }

    k
}

fn main() {}

} // verus!

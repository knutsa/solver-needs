use vstd::prelude::*;

verus! {

// Sum of elements in a sequence
pub open spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        sum_seq(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    }
}

// Sum of seats for coalition members (coalition contains 1-indexed party numbers)
pub open spec fn coalition_seat_sum(a: Seq<int>, coalition: Seq<int>) -> int
    decreases coalition.len(),
{
    if coalition.len() == 0 {
        0
    } else if 1 <= coalition[coalition.len() - 1] && coalition[coalition.len() - 1] <= a.len() {
        coalition_seat_sum(a, coalition.subrange(0, coalition.len() - 1))
            + a[coalition[coalition.len() - 1] - 1]
    } else {
        coalition_seat_sum(a, coalition.subrange(0, coalition.len() - 1))
    }
}

// A coalition is valid per the problem statement
pub open spec fn is_valid_coalition(n: int, a: Seq<int>, coalition: Seq<int>) -> bool
    recommends a.len() == n && n >= 1,
{
    &&& (forall|i: int| 0 <= i < coalition.len() ==> 1 <= #[trigger] coalition[i] && coalition[i] <= n)
    &&& (forall|i: int, j: int|
        0 <= i < coalition.len() && 0 <= j < coalition.len() && i != j
            ==> #[trigger] coalition[i] != #[trigger] coalition[j])
    &&& (exists|i: int| 0 <= i < coalition.len() && #[trigger] coalition[i] == 1)
    &&& (forall|i: int|
        0 <= i < coalition.len()
            ==> #[trigger] coalition[i] == 1 || a[0] >= 2 * a[coalition[i] - 1])
    &&& coalition_seat_sum(a, coalition) * 2 > sum_seq(a)
}

// Sum of seats of all parties eligible to join Alice's coalition.
pub open spec fn eligible_sum(a: Seq<int>) -> int
    recommends a.len() >= 1,
    decreases a.len(),
{
    if a.len() <= 1 {
        if a.len() == 1 { a[0] } else { 0 }
    } else if a[a.len() - 1] * 2 <= a[0] {
        eligible_sum(a.subrange(0, a.len() - 1)) + a[a.len() - 1]
    } else {
        eligible_sum(a.subrange(0, a.len() - 1))
    }
}

// No valid coalition can exist
pub open spec fn no_valid_coalition_possible(n: int, a: Seq<int>) -> bool
    recommends a.len() == n && n >= 1,
{
    eligible_sum(a) * 2 <= sum_seq(a)
}

// --- Helper Lemmas ---

proof fn sum_seq_subrange_step(s: Seq<int>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        sum_seq(s.subrange(0, i + 1)) == sum_seq(s.subrange(0, i)) + s[i],
{
    let s1 = s.subrange(0, i + 1);
    assert(s1.len() == i + 1);
    assert(s1[s1.len() - 1] == s[i]);
    assert(s1.subrange(0, s1.len() - 1) =~= s.subrange(0, i));
}

proof fn coalition_seat_sum_singleton(a: Seq<int>, v: int)
    requires
        1 <= v <= a.len(),
    ensures
        coalition_seat_sum(a, seq![v]) == a[v - 1],
{
    let c = seq![v];
    // c has length 1, c[0] == v, and 1 <= v <= a.len()
    // The recursive step: coalition_seat_sum(a, c) unfolds to
    //   coalition_seat_sum(a, c.subrange(0, 0)) + a[v - 1]
    // = coalition_seat_sum(a, empty) + a[v - 1]
    // = 0 + a[v - 1]
    assert(c.subrange(0, 0) =~= Seq::<int>::empty());
    // Need to show that coalition_seat_sum on empty is 0
    assert(coalition_seat_sum(a, Seq::<int>::empty()) == 0);
}

proof fn coalition_seat_sum_append(a: Seq<int>, c: Seq<int>, v: int)
    requires
        1 <= v <= a.len(),
    ensures
        coalition_seat_sum(a, c.push(v)) == coalition_seat_sum(a, c) + a[v - 1],
{
    let cp = c.push(v);
    assert(cp.len() == c.len() + 1);
    assert(cp[cp.len() - 1] == v);
    assert(cp.subrange(0, cp.len() - 1) =~= c);
}

proof fn eligible_sum_step(a: Seq<int>, j: int)
    requires
        a.len() >= 1,
        1 <= j < a.len(),
    ensures
        eligible_sum(a.subrange(0, j + 1))
            == (if a[j] * 2 <= a[0] {
                eligible_sum(a.subrange(0, j)) + a[j]
            } else {
                eligible_sum(a.subrange(0, j))
            }),
{
    let s = a.subrange(0, j + 1);
    assert(s.len() == j + 1);
    assert(s[s.len() - 1] == a[j]);
    assert(s[0] == a[0]);
    assert(s.subrange(0, s.len() - 1) =~= a.subrange(0, j));
}

proof fn eligible_sum_base(a: Seq<int>)
    requires
        a.len() >= 1,
    ensures
        eligible_sum(a.subrange(0, 1)) == a[0],
{
    let s = a.subrange(0, 1);
    assert(s.len() == 1);
    assert(s[0] == a[0]);
}

// Helper: sum_seq of non-negative elements is non-negative
proof fn sum_seq_nonneg(s: Seq<int>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
    ensures
        sum_seq(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        assert(s.subrange(0, s.len() - 1).len() == s.len() - 1);
        let sub = s.subrange(0, s.len() - 1);
        assert(forall|i: int| 0 <= i < sub.len() ==> #[trigger] sub[i] >= 0);
        sum_seq_nonneg(sub);
    }
}

fn prime_minister(n: i64, a: &Vec<i64>) -> (result: (i64, Vec<i64>))
    requires
        n >= 1,
        n <= 1_000,
        a.len() == n,
        forall|i: int| 0 <= i < n ==> 0 <= #[trigger] a[i] < 1_000_000,
    ensures
        ({
            let (k, coalition) = result;
            &&& (k > 0 ==> (k == coalition.len()
                && is_valid_coalition(n as int, a@.map(|_i: int, x: i64| x as int),
                    coalition@.map(|_i: int, x: i64| x as int))))
            &&& (k == 0 ==> (coalition.len() == 0
                && no_valid_coalition_possible(n as int, a@.map(|_i: int, x: i64| x as int))))
        }),
{
    let ghost a_spec: Seq<int> = a@.map(|_i: int, x: i64| x as int);

    // Step 1: Compute total sum of all seats
    let mut total_sum: i64 = 0;
    let mut i: i64 = 0;

    while i < n
        invariant
            0 <= i <= n,
            n >= 1,
            n <= 1_000,
            a.len() == n,
            forall|j: int| 0 <= j < n ==> 0 <= #[trigger] a[j] < 1_000_000,
            total_sum == sum_seq(a_spec.subrange(0, i as int)),
            a_spec =~= a@.map(|_i: int, x: i64| x as int),
            total_sum >= 0,
            total_sum <= i * 1_000_000,
        decreases n - i,
    {
        proof {
            sum_seq_subrange_step(a_spec, i as int);
        }
        total_sum = total_sum + a[i as usize];
        i = i + 1;
    }
    proof {
        assert(a_spec.subrange(0, n as int) =~= a_spec);
    }

    // Step 2: Build coalition with all eligible parties
    let mut coalition: Vec<i64> = Vec::new();
    coalition.push(1);
    let mut coal_sum: i64 = a[0];

    let ghost mut coalition_spec: Seq<int> = seq![1int];

    proof {
        coalition_seat_sum_singleton(a_spec, 1);
        eligible_sum_base(a_spec);
        assert(coalition_spec =~= coalition@.map(|_i: int, x: i64| x as int));
    }

    let mut j: i64 = 1;
    while j < n
        invariant
            1 <= j <= n,
            n >= 1,
            n <= 1_000,
            a.len() == n,
            forall|idx: int| 0 <= idx < n ==> 0 <= #[trigger] a[idx] < 1_000_000,
            a_spec =~= a@.map(|_i: int, x: i64| x as int),
            coalition.len() >= 1,
            coalition_spec =~= coalition@.map(|_i: int, x: i64| x as int),
            coalition_spec[0] == 1,
            forall|p: int| 0 <= p < coalition_spec.len() ==> 1 <= #[trigger] coalition_spec[p] && coalition_spec[p] <= j,
            forall|p: int, q: int|
                0 <= p < coalition_spec.len() && 0 <= q < coalition_spec.len() && p != q
                    ==> #[trigger] coalition_spec[p] != #[trigger] coalition_spec[q],
            coal_sum == coalition_seat_sum(a_spec, coalition_spec),
            coal_sum == eligible_sum(a_spec.subrange(0, j as int)),
            forall|p: int|
                0 <= p < coalition_spec.len()
                    ==> #[trigger] coalition_spec[p] == 1 || a_spec[0] >= 2 * a_spec[coalition_spec[p] - 1],
            coal_sum >= 0,
            coal_sum <= j * 1_000_000,
            coalition.len() <= j,
        decreases n - j,
    {
        proof {
            eligible_sum_step(a_spec, j as int);
        }
        if a[j as usize] * 2 <= a[0] {
            proof {
                assert(forall|p: int| 0 <= p < coalition_spec.len() ==> #[trigger] coalition_spec[p] <= j < j + 1);
                coalition_seat_sum_append(a_spec, coalition_spec, (j + 1) as int);
            }
            coalition.push((j + 1) as i64);
            coal_sum = coal_sum + a[j as usize];
            proof {
                coalition_spec = coalition_spec.push((j + 1) as int);
                assert(coalition_spec =~= coalition@.map(|_i: int, x: i64| x as int));
            }
        }
        j = j + 1;
    }
    proof {
        assert(a_spec.subrange(0, n as int) =~= a_spec);
    }

    // Step 3: Check if coalition has strict majority
    if coal_sum * 2 > total_sum {
        let k = coalition.len() as i64;
        proof {
            assert(coalition_spec[0] == 1);
            assert(is_valid_coalition(n as int, a_spec, coalition_spec));
        }
        (k, coalition)
    } else {
        proof {
            assert(no_valid_coalition_possible(n as int, a_spec));
        }
        let empty: Vec<i64> = Vec::new();
        (0, empty)
    }
}

fn main() {}

} // verus!

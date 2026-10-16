use vstd::prelude::*;

verus! {

spec fn sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        sum(s.drop_last()) + s.last()
    }
}

spec fn occupancy(a: Seq<int>, b: Seq<int>) -> int
{
    sum(b) - sum(a)
}

spec fn is_valid_capacity(c: int, n: int, a: Seq<int>, b: Seq<int>) -> bool
{
    c >= 0
    && forall|k: int| 1 <= k <= n ==> occupancy(#[trigger] a.take(k), b.take(k)) <= c
}

spec fn is_minimum_capacity(c: int, n: int, a: Seq<int>, b: Seq<int>) -> bool
{
    is_valid_capacity(c, n, a, b)
    && forall|c_prime: int| 0 <= c_prime < c ==> !is_valid_capacity(c_prime, n, a, b)
}

proof fn sum_append(s: Seq<int>, x: int)
    ensures
        sum(s.push(x)) == sum(s) + x,
{
    let t = s.push(x);
    assert(t.len() > 0);
    assert(t.drop_last() =~= s);
    assert(t.last() == x);
}

proof fn tram_proof(n: int, a: Seq<int>, b: Seq<int>) -> (capacity: int)
    requires
        0 <= n <= a.len(),
        n <= b.len(),
    ensures
        is_minimum_capacity(capacity, n, a, b),
    decreases n,
{
    if n == 0 {
        assert(is_valid_capacity(0, 0, a, b));
        return 0;
    }

    let prev_cap = tram_proof(n - 1, a, b);

    assert(a.take(n).drop_last() =~= a.take(n - 1));
    assert(b.take(n).drop_last() =~= b.take(n - 1));
    assert(a.take(n) =~= a.take(n - 1).push(a[n - 1]));
    assert(b.take(n) =~= b.take(n - 1).push(b[n - 1]));
    sum_append(a.take(n - 1), a[n - 1]);
    sum_append(b.take(n - 1), b[n - 1]);

    let occ_n = occupancy(a.take(n), b.take(n));

    if occ_n > prev_cap {
        assert(forall|k: int| 1 <= k <= n - 1 ==> occupancy(#[trigger] a.take(k), b.take(k)) <= prev_cap);
        assert(forall|k: int| 1 <= k <= n - 1 ==> occupancy(#[trigger] a.take(k), b.take(k)) <= occ_n);
        assert(occupancy(a.take(n), b.take(n)) <= occ_n);
        assert(is_valid_capacity(occ_n, n, a, b));
        assert(forall|c_prime: int| 0 <= c_prime < occ_n ==> !is_valid_capacity(c_prime, n, a, b));
        return occ_n;
    } else {
        assert(forall|k: int| 1 <= k <= n - 1 ==> occupancy(#[trigger] a.take(k), b.take(k)) <= prev_cap);
        assert(occupancy(a.take(n), b.take(n)) <= prev_cap);
        assert(is_valid_capacity(prev_cap, n, a, b));

        assert(forall|c_prime: int| 0 <= c_prime < prev_cap ==> !is_valid_capacity(c_prime, n, a, b))
            by {
                assert forall|c_prime: int| 0 <= c_prime < prev_cap implies !is_valid_capacity(c_prime, n, a, b) by {
                    if is_valid_capacity(c_prime, n, a, b) {
                        assert(forall|k: int| 1 <= k <= n - 1 ==> occupancy(#[trigger] a.take(k), b.take(k)) <= c_prime);
                        assert(is_valid_capacity(c_prime, n - 1, a, b));
                    }
                };
            };

        return prev_cap;
    }
}

fn tram(n: i64, a: &Vec<i64>, b: &Vec<i64>) -> (capacity: i64)
    requires
        0 <= n <= a@.len(),
        n <= b@.len(),
        forall|i: int| 0 <= i < a@.len() ==> -1_000_000 <= #[trigger] a@[i] <= 1_000_000,
        forall|i: int| 0 <= i < b@.len() ==> -1_000_000 <= #[trigger] b@[i] <= 1_000_000,
        n <= 100_000,
    ensures
        is_minimum_capacity(capacity as int, n as int, a@.map(|_idx, x: i64| x as int), b@.map(|_idx, x: i64| x as int)),
{
    let ghost a_spec: Seq<int> = a@.map(|_idx, x: i64| x as int);
    let ghost b_spec: Seq<int> = b@.map(|_idx, x: i64| x as int);

    let mut current: i64 = 0;
    let mut capacity: i64 = 0;
    let mut i: i64 = 0;
    // Ghost tracking of sums for overflow reasoning
    let ghost mut sum_a: int = 0;
    let ghost mut sum_b: int = 0;

    proof {
        assert(a_spec.take(0) =~= Seq::<int>::empty());
        assert(b_spec.take(0) =~= Seq::<int>::empty());
    }

    while i < n
        invariant
            0 <= i <= n,
            n <= a@.len(),
            n <= b@.len(),
            n <= 100_000,
            a_spec == a@.map(|_idx, x: i64| x as int),
            b_spec == b@.map(|_idx, x: i64| x as int),
            current as int == occupancy(a_spec.take(i as int), b_spec.take(i as int)),
            capacity >= 0,
            forall|k: int| 1 <= k <= i ==> occupancy(#[trigger] a_spec.take(k), b_spec.take(k)) <= capacity,
            capacity == 0 || exists|k: int| 1 <= k <= i && capacity as int == occupancy(#[trigger] a_spec.take(k), b_spec.take(k)),
            forall|j: int| 0 <= j < a@.len() ==> -1_000_000 <= #[trigger] a@[j] <= 1_000_000,
            forall|j: int| 0 <= j < b@.len() ==> -1_000_000 <= #[trigger] b@[j] <= 1_000_000,
            forall|j: int| 0 <= j < a_spec.len() ==> -1_000_000 <= #[trigger] a_spec[j] <= 1_000_000,
            forall|j: int| 0 <= j < b_spec.len() ==> -1_000_000 <= #[trigger] b_spec[j] <= 1_000_000,
            sum_a == sum(a_spec.take(i as int)),
            sum_b == sum(b_spec.take(i as int)),
            // Track sum bounds directly via ghost vars (avoids nonlinear arithmetic)
            -1_000_000 * i <= sum_a <= 1_000_000 * i,
            -1_000_000 * i <= sum_b <= 1_000_000 * i,
            current as int == sum_b - sum_a,
        decreases n - i,
    {
        proof {
            assert(a_spec.take((i + 1) as int).drop_last() =~= a_spec.take(i as int));
            assert(b_spec.take((i + 1) as int).drop_last() =~= b_spec.take(i as int));

            assert(a_spec.take((i + 1) as int) =~= a_spec.take(i as int).push(a_spec[i as int]));
            assert(b_spec.take((i + 1) as int) =~= b_spec.take(i as int).push(b_spec[i as int]));

            sum_append(a_spec.take(i as int), a_spec[i as int]);
            sum_append(b_spec.take(i as int), b_spec[i as int]);

            assert(a_spec[i as int] == a@[i as int] as int);
            assert(b_spec[i as int] == b@[i as int] as int);

            assert(-1_000_000 <= a_spec[i as int] <= 1_000_000);
            assert(-1_000_000 <= b_spec[i as int] <= 1_000_000);

            sum_a = sum_a + a_spec[i as int];
            sum_b = sum_b + b_spec[i as int];

            // New bounds: sum_a in [-1M*(i+1), 1M*(i+1)]
            // -1M*i - 1M <= sum_a <= 1M*i + 1M = -1M*(i+1) ... 1M*(i+1)
        }

        current = current - a[i as usize] + b[i as usize];

        if current > capacity {
            capacity = current;
        }
        i = i + 1;
    }

    proof {
        if capacity > 0 {
            let k_witness = choose|k: int| 1 <= k <= i && capacity as int == occupancy(#[trigger] a_spec.take(k), b_spec.take(k));
            assert(1 <= k_witness <= n as int);
            assert(capacity as int == occupancy(a_spec.take(k_witness), b_spec.take(k_witness)));
            assert(forall|c_prime: int| 0 <= c_prime < capacity as int ==> !is_valid_capacity(c_prime, n as int, a_spec, b_spec));
        }
    }

    capacity
}

fn main() {}

} // verus!

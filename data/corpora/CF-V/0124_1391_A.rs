use vstd::prelude::*;

verus! {

// --- Spec: Bitwise OR for non-negative integers ---
pub open spec fn bitwise_or(a: int, b: int) -> int
    recommends a >= 0 && b >= 0,
    decreases a + b
    when a >= 0 && b >= 0
{
    if a == 0 && b == 0 { 0int }
    else {
        (if a % 2 == 1 || b % 2 == 1 { 1int } else { 0int }) + 2 * bitwise_or(a / 2, b / 2)
    }
}

// --- Spec: OR of all elements in a non-empty sequence ---
pub open spec fn or_of_seq(s: Seq<int>) -> int
    recommends s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
    decreases s.len()
    when s.len() > 0
{
    if s.len() == 1 { s[0] }
    else { bitwise_or(or_of_seq(s.subrange(0, s.len() as int - 1)), s[s.len() as int - 1]) }
}

// --- Spec: p is a permutation of [1..n] ---
pub open spec fn is_permutation(p: Seq<int>, n: int) -> bool {
    n >= 0 &&
    p.len() == n &&
    (forall|i: int| 0 <= i < n ==> 1 <= #[trigger] p[i] && p[i] <= n) &&
    (forall|i: int, j: int| 0 <= i < j < n ==> #[trigger] p[i] != #[trigger] p[j])
}

// --- Spec: every subarray's bitwise OR >= the subarray's length ---
pub open spec fn is_good(p: Seq<int>) -> bool {
    (forall|k: int| 0 <= k < p.len() ==> #[trigger] p[k] >= 0) &&
    (forall|i: int, j: int| 0 <= i <= j < p.len() ==>
        #[trigger] or_of_seq(p.subrange(i, j + 1)) >= j - i + 1)
}

// --- Helper lemma: bitwise_or(a, b) >= 0 ---
proof fn bitwise_or_nonneg(a: int, b: int)
    requires a >= 0, b >= 0,
    ensures bitwise_or(a, b) >= 0,
    decreases a + b,
{
    if a == 0 && b == 0 {
    } else {
        bitwise_or_nonneg(a / 2, b / 2);
    }
}

// --- Helper lemma: or_of_seq(s) >= 0 ---
proof fn or_of_seq_nonneg(s: Seq<int>)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
    ensures
        or_of_seq(s) >= 0,
    decreases s.len(),
{
    if s.len() == 1 {
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        assert forall|i: int| 0 <= i < prefix.len() implies prefix[i] >= 0 by {
            assert(prefix[i] == s[i]);
        };
        or_of_seq_nonneg(prefix);
        bitwise_or_nonneg(or_of_seq(prefix), s[s.len() as int - 1]);
    }
}

// --- Helper lemma: BitwiseOr(a, b) >= a ---
proof fn bitwise_or_geq_left(a: int, b: int)
    requires a >= 0, b >= 0,
    ensures bitwise_or(a, b) >= a,
    decreases a + b,
{
    if a == 0 && b == 0 {
    } else {
        bitwise_or_geq_left(a / 2, b / 2);
    }
}

// --- Helper lemma: BitwiseOr(a, b) >= b ---
proof fn bitwise_or_geq_right(a: int, b: int)
    requires a >= 0, b >= 0,
    ensures bitwise_or(a, b) >= b,
    decreases a + b,
{
    if a == 0 && b == 0 {
    } else {
        bitwise_or_geq_right(a / 2, b / 2);
    }
}

// --- Helper lemma: OrOfSeq(s) >= s[idx] ---
proof fn or_of_seq_geq_element(s: Seq<int>, idx: int)
    requires
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> s[i] >= 0,
        0 <= idx < s.len(),
    ensures
        or_of_seq(s) >= s[idx],
    decreases s.len(),
{
    if s.len() == 1 {
    } else if idx == s.len() as int - 1 {
        let prefix = s.subrange(0, s.len() as int - 1);
        assert forall|i: int| 0 <= i < prefix.len() implies prefix[i] >= 0 by {
            assert(prefix[i] == s[i]);
        };
        or_of_seq_nonneg(prefix);
        bitwise_or_geq_right(or_of_seq(prefix), s[s.len() as int - 1]);
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        assert forall|i: int| 0 <= i < prefix.len() implies prefix[i] >= 0 by {
            assert(prefix[i] == s[i]);
        };
        assert(prefix[idx] == s[idx]);
        or_of_seq_geq_element(prefix, idx);
        or_of_seq_nonneg(prefix);
        bitwise_or_geq_left(or_of_seq(prefix), s[s.len() as int - 1]);
    }
}

// --- Main method: GoodPermutation ---
fn good_permutation(n: i64) -> (p: Vec<i64>)
    requires
        n >= 1,
        n <= 1_000_000, // bound for overflow safety
    ensures
        is_permutation(p@.map(|_idx: int, v: i64| v as int), n as int),
        is_good(p@.map(|_idx: int, v: i64| v as int)),
{
    let mut p: Vec<i64> = Vec::new();
    let mut i: i64 = 1;

    while i <= n
        invariant
            1 <= i <= n + 1,
            n <= 1_000_000,
            p@.len() == (i - 1) as nat,
            forall|k: int| 0 <= k < p@.len() ==> #[trigger] p@[k] == (k + 1) as i64,
        decreases (n - i + 1),
    {
        p.push(i);
        i = i + 1;
    }

    let ghost ps: Seq<int> = p@.map(|_idx: int, v: i64| v as int);

    proof {
        assert(ps.len() == n as int);
        assert forall|k: int| 0 <= k < n implies #[trigger] ps[k] == k + 1 by {
            assert(p@[k] == (k + 1) as i64);
        };

        // Prove IsPermutation
        assert forall|k: int| 0 <= k < n implies 1 <= #[trigger] ps[k] && ps[k] <= n by {};
        assert forall|i2: int, j2: int| 0 <= i2 < j2 < n implies #[trigger] ps[i2] != #[trigger] ps[j2] by {};

        // Prove IsGood: every subarray's OR >= its length
        assert forall|k: int| 0 <= k < ps.len() implies #[trigger] ps[k] >= 0 by {};

        assert forall|ii: int, jj: int| 0 <= ii <= jj < ps.len() implies
            #[trigger] or_of_seq(ps.subrange(ii, jj + 1)) >= jj - ii + 1
        by {
            let sub = ps.subrange(ii, jj + 1);
            assert(sub.len() == jj - ii + 1);
            assert(sub.len() > 0);
            assert forall|k: int| 0 <= k < sub.len() implies sub[k] >= 0 by {
                assert(sub[k] == ps[ii + k]);
            };
            // sub[jj - ii] == ps[jj] == jj + 1 >= jj - ii + 1 (since ii >= 0)
            assert(sub[jj - ii] == ps[jj]);
            assert(ps[jj] == jj + 1);
            assert(sub[jj - ii] == jj + 1);
            assert(jj + 1 >= jj - ii + 1);
            or_of_seq_geq_element(sub, jj - ii);
        };
    }

    p
}

fn main() {}

} // verus!

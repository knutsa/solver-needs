use vstd::prelude::*;

verus! {

// Sum of all elements in a sequence
pub open spec fn sum_seq(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        sum_seq(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    }
}

// Every person receives at least one item
pub open spec fn all_at_least_one(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] >= 1
}

// A valid distribution of `supply` items among `n` people, each getting at least 1
pub open spec fn valid_distribution(dist: Seq<int>, n: int, supply: int) -> bool {
    n >= 0
    && dist.len() == n
    && all_at_least_one(dist)
    && sum_seq(dist) <= supply
}

// A valid rewarding: valid distributions of both pens and notebooks
pub open spec fn valid_rewarding(
    pen_dist: Seq<int>,
    note_dist: Seq<int>,
    n: int,
    m: int,
    k: int,
) -> bool {
    valid_distribution(pen_dist, n, m) && valid_distribution(note_dist, n, k)
}

// The minimal-cost distribution: give exactly 1 item to each person
pub open spec fn uniform_dist(n: nat) -> Seq<int>
    decreases n,
{
    if n == 0 {
        Seq::<int>::empty()
    } else {
        uniform_dist((n - 1) as nat).push(1)
    }
}

// Lemma: uniform_dist has length n
proof fn lemma_uniform_dist_len(n: nat)
    ensures
        uniform_dist(n).len() == n,
    decreases n,
{
    if n > 0 {
        lemma_uniform_dist_len((n - 1) as nat);
    }
}

// Lemma: all elements of uniform_dist are 1
proof fn lemma_uniform_dist_all_one(n: nat)
    ensures
        forall|i: int| 0 <= i < uniform_dist(n).len() ==> uniform_dist(n)[i] == 1,
    decreases n,
{
    if n > 0 {
        lemma_uniform_dist_all_one((n - 1) as nat);
        let prev = uniform_dist((n - 1) as nat);
        let curr = prev.push(1);
        assert(curr.len() == prev.len() + 1);
        assert forall|i: int| 0 <= i < curr.len() implies curr[i] == 1 by {
            if i < prev.len() as int {
                assert(curr[i] == prev[i]);
            } else {
                assert(curr[i] == 1);
            }
        }
    }
}

// Lemma: sum of uniform_dist(n) == n
proof fn lemma_uniform_dist_sum(n: nat)
    ensures
        sum_seq(uniform_dist(n)) == n as int,
    decreases n,
{
    if n == 0 {
    } else {
        lemma_uniform_dist_sum((n - 1) as nat);
        let prev = uniform_dist((n - 1) as nat);
        let curr = prev.push(1);
        lemma_uniform_dist_len(n);
        // curr.subrange(0, curr.len() - 1) == prev
        assert(curr.subrange(0, curr.len() - 1) =~= prev);
        assert(curr[curr.len() - 1] == 1);
    }
}

// Mathematical fact: any distribution giving everyone >= 1 item uses >= n items total.
proof fn lemma_sum_lower_bound(s: Seq<int>)
    ensures
        all_at_least_one(s) ==> sum_seq(s) >= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        let prefix = s.subrange(0, s.len() - 1);
        lemma_sum_lower_bound(prefix);
        if all_at_least_one(s) {
            assert forall|i: int| 0 <= i < prefix.len() implies prefix[i] >= 1 by {
                assert(prefix[i] == s[i]);
            }
        }
    }
}

fn vus_contest(n: i64, m: i64, k: i64) -> (result: bool)
    requires
        n >= 1,
    ensures
        result == valid_rewarding(uniform_dist(n as nat), uniform_dist(n as nat), n as int, m as int, k as int),
{
    proof {
        lemma_uniform_dist_len(n as nat);
        lemma_uniform_dist_all_one(n as nat);
        lemma_uniform_dist_sum(n as nat);
        // If k < n or m < n, no valid distribution exists
        // since any distribution needs at least n items
        if k < n || m < n {
            // Need to show that ValidRewarding is false
            // Since uniform_dist(n) sums to n, and n > supply, it fails
        } else {
            // uniform_dist(n) works for both
        }
    }
    if k < n || m < n {
        false
    } else {
        true
    }
}

fn main() {}

} // verus!

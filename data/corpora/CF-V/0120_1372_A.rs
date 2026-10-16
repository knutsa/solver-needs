use vstd::prelude::*;

verus! {

spec fn in_range(a: Seq<int>) -> bool {
    forall|i: int| 0 <= i < a.len() ==> 1 <= a[i] && a[i] <= 1000
}

spec fn no_triple_sum(a: Seq<int>) -> bool {
    forall|x: int, y: int, z: int|
        (0 <= x < a.len() && 0 <= y < a.len() && 0 <= z < a.len()) ==>
        a[x] + a[y] != a[z]
}

spec fn is_complete(a: Seq<int>) -> bool {
    in_range(a) && no_triple_sum(a)
}

#[verifier::loop_isolation(false)]
fn solve(n: i64) -> (a: Vec<i64>)
    requires n >= 0
    ensures
        a@.len() == n as int,
        is_complete(a@.map_values(|x: i64| x as int)),
{
    let mut a: Vec<i64> = Vec::new();
    let mut i: i64 = 0;
    while i < n
        invariant
            0 <= i,
            i <= n,
            i as int == a@.len(),
            forall|j: int| 0 <= j < a@.len() ==> a@[j] == 1i64,
        decreases n - i,
    {
        a.push(1i64);
        i = i + 1;
    }
    proof {
        let mapped = a@.map_values(|x: i64| x as int);
        assert forall|k: int| 0 <= k < mapped.len() implies mapped[k] == 1 by {
            assert(a@[k] == 1i64);
        };
        assert(in_range(mapped)) by {
            assert forall|k: int| 0 <= k < mapped.len() implies 1 <= mapped[k] && mapped[k] <= 1000 by {};
        };
        assert(no_triple_sum(mapped)) by {
            assert forall|x: int, y: int, z: int|
                (0 <= x < mapped.len() && 0 <= y < mapped.len() && 0 <= z < mapped.len()) implies
                mapped[x] + mapped[y] != mapped[z] by {};
        };
        assert(is_complete(mapped));
    }
    a
}

#[verifier::loop_isolation(false)]
fn test_solve(ns: &Vec<i64>)
    requires forall|i: int| 0 <= i < ns@.len() ==> ns@[i] >= 0,
{
    let mut i: usize = 0;
    while i < ns.len()
        invariant
            i <= ns@.len(),
        decreases ns.len() - i,
    {
        let r = solve(ns[i]);
        let mut j: usize = 0;
        while j < r.len()
            invariant
                j <= r@.len(),
            decreases r.len() - j,
        {
            j = j + 1;
        }
        i = i + 1;
    }
}

fn main() {}

} // verus!
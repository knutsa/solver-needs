use vstd::prelude::*;

verus! {

// ghost function Sum
spec fn sum(s: Seq<int>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1]
    }
}

// ghost predicate AllNonNeg
spec fn all_non_neg(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] >= 0
}

// ghost predicate LegalStep
spec fn legal_step(before: Seq<int>, after: Seq<int>) -> bool {
    before.len() == after.len()
        && (
        (exists|i: int|
            0 <= i < before.len()
                && before[i] > 0
                && after =~= before.update(i, before[i] - 1))
        ||
        (exists|i: int|
            #![trigger before[i]]
            0 <= i < before.len()
                && before[i] > 0
                && (exists|j: int|
                    #![trigger before[j]]
                    0 <= j < before.len()
                        && i != j
                        && after =~= before.update(i, before[i] - 1).update(j, before[j] + 1)))
    )
}

// ghost predicate IsValidPath
spec fn is_valid_path(path: Seq<Seq<int>>) -> bool {
    path.len() >= 1
        && (forall|k: int| 0 <= k < path.len() - 1 ==> #[trigger] legal_step(path[k], path[k + 1]))
}

// ghost predicate ValidRemoval
spec fn valid_removal(x: Seq<int>, kept: Seq<int>, target_sum: int) -> bool {
    kept.len() == x.len()
        && (forall|i: int| 0 <= i < x.len() ==> (0 <= kept[i] && kept[i] <= x[i]))
        && sum(kept) == target_sum
}

// ghost function GreedyKeep
spec fn greedy_keep(x: Seq<int>, remaining: int) -> Seq<int>
    decreases x.len(),
{
    if x.len() == 0 {
        Seq::<int>::empty()
    } else {
        let keep = if remaining <= 0 {
            0int
        } else if remaining >= x[0] {
            x[0]
        } else {
            remaining
        };
        Seq::<int>::new(1, |_i: int| keep).add(greedy_keep(x.subrange(1, x.len() as int), remaining - keep))
    }
}

// ghost predicate CanTransform
spec fn can_transform(x: Seq<int>, y: Seq<int>) -> bool {
    x.len() == y.len()
        && all_non_neg(x)
        && all_non_neg(y)
        && valid_removal(x, greedy_keep(x, sum(y)), sum(y))
}

// ---- Helper Lemmas ----

// lemma SumAppend
proof fn sum_append(s: Seq<int>, v: int)
    ensures
        sum(s.push(v)) == sum(s) + v,
{
    let t = s.push(v);
    assert(t.subrange(0, t.len() - 1) =~= s);
}

// lemma SumCons: Sum(s) == s[0] + Sum(s[1..])
// We prove this by induction on s.len().
proof fn sum_cons(s: Seq<int>)
    requires
        s.len() > 0,
    ensures
        sum(s) == s[0] + sum(s.subrange(1, s.len() as int)),
    decreases s.len(),
{
    let tail = s.subrange(1, s.len() as int);
    if s.len() == 1 {
        assert(tail =~= Seq::<int>::empty());
        // sum(s) = sum(s[..0]) + s[0] = 0 + s[0]
        assert(s.subrange(0, 0int) =~= Seq::<int>::empty());
    } else {
        // sum(s) = sum(s[..n-1]) + s[n-1]  (by definition)
        let prefix = s.subrange(0, s.len() - 1);
        // By IH: sum(prefix) = prefix[0] + sum(prefix[1..])
        sum_cons(prefix);
        assert(prefix[0] == s[0]);
        assert(prefix.subrange(1, prefix.len() as int) =~= s.subrange(1, s.len() - 1));
        // So sum(prefix) = s[0] + sum(s[1..n-1])
        // And sum(s) = s[0] + sum(s[1..n-1]) + s[n-1]
        // We need: sum(tail) = sum(s[1..n-1]) + s[n-1]
        // This is just the definition of sum on tail:
        // sum(tail) = sum(tail[..tail.len()-1]) + tail[tail.len()-1]
        assert(tail.subrange(0, tail.len() - 1) =~= s.subrange(1, s.len() - 1));
        assert(tail[tail.len() - 1] == s[s.len() - 1]);
        // Now sum(s) = sum(prefix) + s[n-1]
        //            = s[0] + sum(s[1..n-1]) + s[n-1]
        //            = s[0] + sum(tail)
    }
}

// lemma SumNonNeg
proof fn sum_non_neg(s: Seq<int>)
    requires
        all_non_neg(s),
    ensures
        sum(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        let prefix = s.subrange(0, s.len() - 1);
        assert(all_non_neg(prefix)) by {
            assert forall|i: int| 0 <= i < prefix.len() implies #[trigger] prefix[i] >= 0 by {
                assert(prefix[i] == s[i]);
            }
        };
        sum_non_neg(prefix);
    }
}

// lemma GreedyKeepLength
proof fn greedy_keep_length(x: Seq<int>, r: int)
    ensures
        greedy_keep(x, r).len() == x.len(),
    decreases x.len(),
{
    if x.len() > 0 {
        let keep = if r <= 0 { 0int } else if r >= x[0] { x[0] } else { r };
        greedy_keep_length(x.subrange(1, x.len() as int), r - keep);
    }
}

// lemma GreedyKeepValid
proof fn greedy_keep_valid(x: Seq<int>, r: int)
    requires
        all_non_neg(x),
        0 <= r <= sum(x),
    ensures
        greedy_keep(x, r).len() == x.len(),
        forall|i: int| 0 <= i < x.len() ==> (0 <= #[trigger] greedy_keep(x, r)[i] && greedy_keep(x, r)[i] <= x[i]),
        sum(greedy_keep(x, r)) == r,
    decreases x.len(),
{
    greedy_keep_length(x, r);
    if x.len() == 0 {
    } else {
        let keep = if r <= 0 { 0int } else if r >= x[0] { x[0] } else { r };
        let gk = greedy_keep(x, r);
        let tail_x = x.subrange(1, x.len() as int);

        assert(gk =~= Seq::<int>::new(1, |_i: int| keep).add(greedy_keep(tail_x, r - keep)));

        sum_cons(x);
        assert(all_non_neg(tail_x)) by {
            assert forall|j: int| 0 <= j < tail_x.len() implies #[trigger] tail_x[j] >= 0 by {
                assert(tail_x[j] == x[j + 1]);
            }
        };
        sum_non_neg(tail_x);

        assert(0 <= r - keep <= sum(tail_x));

        greedy_keep_valid(tail_x, r - keep);

        let tail = greedy_keep(tail_x, r - keep);

        assert(gk.len() > 0);
        sum_cons(gk);
        assert(gk[0] == keep);
        assert(gk.subrange(1, gk.len() as int) =~= tail);

        assert forall|i: int| 0 <= i < x.len() implies (0 <= #[trigger] gk[i] && gk[i] <= x[i]) by {
            if i == 0 {
                assert(gk[0] == keep);
                assert(0 <= keep <= x[0]);
            } else {
                assert(gk[i] == tail[i - 1]);
                assert(x[i] == tail_x[i - 1]);
            }
        };
    }
}

// lemma GreedyKeepSumBound
proof fn greedy_keep_sum_bound(x: Seq<int>, r: int)
    requires
        all_non_neg(x),
        r >= 0,
    ensures
        sum(greedy_keep(x, r)) <= sum(x),
        sum(greedy_keep(x, r)) <= r,
    decreases x.len(),
{
    greedy_keep_length(x, r);
    if x.len() == 0 {
    } else {
        let keep = if r <= 0 { 0int } else if r >= x[0] { x[0] } else { r };
        let gk = greedy_keep(x, r);
        let tail_x = x.subrange(1, x.len() as int);

        assert(gk =~= Seq::<int>::new(1, |_i: int| keep).add(greedy_keep(tail_x, r - keep)));

        sum_cons(x);
        assert(all_non_neg(tail_x)) by {
            assert forall|j: int| 0 <= j < tail_x.len() implies #[trigger] tail_x[j] >= 0 by {
                assert(tail_x[j] == x[j + 1]);
            }
        };

        assert(r - keep >= 0);
        greedy_keep_sum_bound(tail_x, r - keep);

        let tail = greedy_keep(tail_x, r - keep);
        assert(gk.len() > 0);
        sum_cons(gk);
        assert(gk[0] == keep);
        assert(gk.subrange(1, gk.len() as int) =~= tail);
        assert(keep <= x[0]);
    }
}

// lemma CanTransformIffSumLeq
proof fn can_transform_iff_sum_leq(x: Seq<int>, y: Seq<int>)
    requires
        x.len() == y.len(),
        all_non_neg(x),
        all_non_neg(y),
    ensures
        can_transform(x, y) <==> sum(y) <= sum(x),
{
    sum_non_neg(y);
    greedy_keep_length(x, sum(y));
    if sum(y) <= sum(x) {
        greedy_keep_valid(x, sum(y));
    } else {
        greedy_keep_sum_bound(x, sum(y));
        // sum(greedy_keep(x, sum(y))) <= sum(x) < sum(y)
        // so sum(greedy_keep(x, sum(y))) != sum(y), meaning valid_removal fails
    }
}

// Helper: relate Vec view to mapped Seq
proof fn vec_map_index(v: &Vec<i64>, s: Seq<int>, idx: int)
    requires
        s =~= v@.map(|_i: int, val: i64| val as int),
        0 <= idx < v.len(),
    ensures
        s[idx] == v[idx] as int,
{
}

// method PilesWithStones (exec)
fn piles_with_stones(x: &Vec<i64>, y: &Vec<i64>) -> (result: bool)
    requires
        x.len() == y.len(),
        all_non_neg(x@.map(|_i: int, v: i64| v as int)),
        all_non_neg(y@.map(|_i: int, v: i64| v as int)),
        forall|i: int| 0 <= i < x.len() ==> 0 <= #[trigger] (x[i] as int) <= 1_000_000_000,
        forall|i: int| 0 <= i < y.len() ==> 0 <= #[trigger] (y[i] as int) <= 1_000_000_000,
        x.len() <= 1_000_000,
    ensures
        result == can_transform(
            x@.map(|_i: int, v: i64| v as int),
            y@.map(|_i: int, v: i64| v as int),
        ),
{
    let ghost xs = x@.map(|_i: int, v: i64| v as int);
    let ghost ys = y@.map(|_i: int, v: i64| v as int);

    let mut x_sum: i64 = 0;
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            xs =~= x@.map(|_i: int, v: i64| v as int),
            x_sum as int == sum(xs.subrange(0, i as int)),
            forall|j: int| 0 <= j < x.len() ==> 0 <= #[trigger] (x[j] as int) <= 1_000_000_000,
            x.len() <= 1_000_000,
            0 <= x_sum,
            x_sum as int <= (i as int) * 1_000_000_000,
        decreases x.len() - i,
    {
        proof {
            let sub = xs.subrange(0, i as int);
            let sub1 = xs.subrange(0, i as int + 1);
            assert(sub1 =~= sub.push(xs[i as int]));
            sum_append(sub, xs[i as int]);
        }
        x_sum = x_sum + x[i];
        i = i + 1;
    }
    proof {
        assert(xs.subrange(0, xs.len() as int) =~= xs);
    }

    let mut y_sum: i64 = 0;
    i = 0;
    while i < y.len()
        invariant
            0 <= i <= y.len(),
            ys =~= y@.map(|_i: int, v: i64| v as int),
            y_sum as int == sum(ys.subrange(0, i as int)),
            forall|j: int| 0 <= j < y.len() ==> 0 <= #[trigger] (y[j] as int) <= 1_000_000_000,
            y.len() <= 1_000_000,
            0 <= y_sum,
            y_sum as int <= (i as int) * 1_000_000_000,
            x.len() == y.len(),
        decreases y.len() - i,
    {
        proof {
            let sub = ys.subrange(0, i as int);
            let sub1 = ys.subrange(0, i as int + 1);
            assert(sub1 =~= sub.push(ys[i as int]));
            sum_append(sub, ys[i as int]);
        }
        y_sum = y_sum + y[i];
        i = i + 1;
    }
    proof {
        assert(ys.subrange(0, ys.len() as int) =~= ys);
        can_transform_iff_sum_leq(xs, ys);
    }
    y_sum <= x_sum
}

fn main() {}

} // verus!

use vstd::prelude::*;

verus! {

pub open spec fn max_int(x: int, y: int) -> int {
    if x >= y { x } else { y }
}

pub open spec fn max_purchases(c: Seq<int>, a: Seq<int>) -> int
    decreases c.len(),
{
    if c.len() == 0 || a.len() == 0 {
        0
    } else if a[0] >= c[0] {
        max_int(1 + max_purchases(c.drop_first(), a.drop_first()), max_purchases(c.drop_first(), a))
    } else {
        max_purchases(c.drop_first(), a)
    }
}

proof fn max_purchases_bound(c: Seq<int>, a: Seq<int>)
    ensures
        0 <= max_purchases(c, a) <= c.len(),
        max_purchases(c, a) <= a.len(),
    decreases c.len(),
{
    if c.len() == 0 || a.len() == 0 {
    } else if a[0] >= c[0] {
        max_purchases_bound(c.drop_first(), a.drop_first());
        max_purchases_bound(c.drop_first(), a);
    } else {
        max_purchases_bound(c.drop_first(), a);
    }
}

proof fn more_games_no_worse(c: Seq<int>, a: Seq<int>)
    requires
        c.len() > 0,
    ensures
        max_purchases(c, a) >= max_purchases(c.drop_first(), a),
{
    if a.len() == 0 {
    } else if a[0] >= c[0] {
        assert(max_purchases(c, a) == max_int(
            1 + max_purchases(c.drop_first(), a.drop_first()),
            max_purchases(c.drop_first(), a),
        ));
    } else {
    }
}

proof fn extra_bill_bounded(c: Seq<int>, a: Seq<int>)
    requires
        a.len() > 0,
    ensures
        max_purchases(c, a) <= max_purchases(c, a.drop_first()) + 1,
    decreases c.len(),
{
    if c.len() == 0 {
    } else {
        extra_bill_bounded(c.drop_first(), a);
        more_games_no_worse(c, a.drop_first());
    }
}

proof fn greedy_buy_optimal(c: Seq<int>, a: Seq<int>)
    requires
        c.len() > 0,
        a.len() > 0,
        a[0] >= c[0],
    ensures
        max_purchases(c, a) == 1 + max_purchases(c.drop_first(), a.drop_first()),
{
    extra_bill_bounded(c.drop_first(), a);
}

fn game_shopping(c: &Vec<i64>, a: &Vec<i64>) -> (count: i64)
    requires
        c@.len() <= i64::MAX as int,
        a@.len() <= i64::MAX as int,
        // All values fit in i64
        forall|k: int| 0 <= k < c@.len() ==> c@[k] == c[k] as int,
        forall|k: int| 0 <= k < a@.len() ==> a@[k] == a[k] as int,
    ensures
        count as int == max_purchases(c@.map_values(|v: i64| v as int), a@.map_values(|v: i64| v as int)),
        0 <= count <= c.len(),
        count <= a.len(),
{
    let mut count: i64 = 0;
    let mut i: usize = 0;
    let mut j: usize = 0;

    let ghost c_spec: Seq<int> = c@.map_values(|v: i64| v as int);
    let ghost a_spec: Seq<int> = a@.map_values(|v: i64| v as int);

    proof {
        assert(c_spec.subrange(0, c_spec.len() as int) =~= c_spec);
        assert(a_spec.subrange(0, a_spec.len() as int) =~= a_spec);
    }

    while i < c.len() && j < a.len()
        invariant
            0 <= i <= c.len(),
            0 <= j <= a.len(),
            count >= 0,
            c_spec == c@.map_values(|v: i64| v as int),
            a_spec == a@.map_values(|v: i64| v as int),
            c_spec.len() == c@.len(),
            a_spec.len() == a@.len(),
            count as int + max_purchases(c_spec.subrange(i as int, c_spec.len() as int), a_spec.subrange(j as int, a_spec.len() as int)) == max_purchases(c_spec, a_spec),
            count as int <= c_spec.len(),
            count as int <= a_spec.len(),
            c@.len() <= i64::MAX as int,
            a@.len() <= i64::MAX as int,
        decreases c.len() - i,
    {
        if a[j] >= c[i] {
            proof {
                let c_sub = c_spec.subrange(i as int, c_spec.len() as int);
                let a_sub = a_spec.subrange(j as int, a_spec.len() as int);
                greedy_buy_optimal(c_sub, a_sub);
                let c_sub_next = c_spec.subrange(i as int + 1, c_spec.len() as int);
                let a_sub_next = a_spec.subrange(j as int + 1, a_spec.len() as int);
                assert(c_sub.drop_first() =~= c_sub_next);
                assert(a_sub.drop_first() =~= a_sub_next);
                // After greedy: count+1 + max_purchases(c_sub_next, a_sub_next) == max_purchases(c_spec, a_spec)
                // Need to show count+1 doesn't overflow
                max_purchases_bound(c_sub_next, a_sub_next);
                max_purchases_bound(c_spec, a_spec);
                // max_purchases(c_sub_next, a_sub_next) >= 0
                // so count+1 <= max_purchases(c_spec, a_spec) <= c_spec.len() <= i64::MAX
            }
            count = count + 1;
            j = j + 1;
        } else {
            proof {
                let c_sub = c_spec.subrange(i as int, c_spec.len() as int);
                let c_sub_next = c_spec.subrange(i as int + 1, c_spec.len() as int);
                let a_sub = a_spec.subrange(j as int, a_spec.len() as int);
                assert(c_sub.drop_first() =~= c_sub_next);
                // In the else branch: max_purchases(c_sub, a_sub) == max_purchases(c_sub_next, a_sub)
                // so count + max_purchases(c_sub_next, a_sub) == max_purchases(c_spec, a_spec)
                max_purchases_bound(c_sub_next, a_sub);
                max_purchases_bound(c_spec, a_spec);
            }
        }
        i = i + 1;
    }
    proof {
        max_purchases_bound(c_spec, a_spec);
    }
    count
}

fn main() {}

} // verus!

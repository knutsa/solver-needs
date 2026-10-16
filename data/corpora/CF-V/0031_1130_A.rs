use vstd::prelude::*;

verus! {

spec fn is_positive_after_div(x: int, d: int) -> bool
    recommends d != 0
{
    (x > 0 && d > 0) || (x < 0 && d < 0)
}

spec fn count_positive_after_div(a: Seq<int>, d: int) -> int
    recommends d != 0
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        count_positive_after_div(a.take(a.len() as int - 1), d)
            + if is_positive_after_div(a[a.len() as int - 1], d) { 1 as int } else { 0 as int }
    }
}

spec fn ceil_half(n: int) -> int {
    (n + 1) / 2
}

spec fn count_positive(a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        count_positive(a.take(a.len() as int - 1))
            + if a[a.len() as int - 1] > 0 { 1 as int } else { 0 as int }
    }
}

spec fn count_negative(a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        count_negative(a.take(a.len() as int - 1))
            + if a[a.len() as int - 1] < 0 { 1 as int } else { 0 as int }
    }
}

spec fn vec_to_spec(a: Seq<i64>) -> Seq<int> {
    a.map(|_idx, x: i64| x as int)
}

proof fn count_pos_div_pos(a: Seq<int>, d: int)
    requires d > 0
    ensures count_positive_after_div(a, d) == count_positive(a)
    decreases a.len()
{
    if a.len() > 0 {
        count_pos_div_pos(a.take(a.len() as int - 1), d);
    }
}

proof fn count_pos_div_neg(a: Seq<int>, d: int)
    requires d < 0
    ensures count_positive_after_div(a, d) == count_negative(a)
    decreases a.len()
{
    if a.len() > 0 {
        count_pos_div_neg(a.take(a.len() as int - 1), d);
    }
}

/// Wrapper spec fn to use as trigger
spec fn cpd(a: Seq<int>, d: int) -> int {
    count_positive_after_div(a, d)
}

proof fn vec_to_spec_index(a: Seq<i64>, i: int)
    requires 0 <= i < a.len()
    ensures vec_to_spec(a)[i] == a[i] as int
{
    assert(vec_to_spec(a)[i] == a.map(|_idx, x: i64| x as int)[i]);
}

proof fn count_positive_step(a: Seq<int>, i: int)
    requires 0 <= i < a.len()
    ensures
        count_positive(a.take(i + 1)) == count_positive(a.take(i))
            + if a[i] > 0 { 1 as int } else { 0 as int }
{
    assert(a.take(i + 1) =~= a.take(i).push(a[i]));
    // Now a.take(i+1).len() == i+1
    // a.take(i+1).take(i) =~= a.take(i)
    // a.take(i+1)[i] == a[i]
    let s = a.take(i + 1);
    assert(s.len() == i + 1);
    assert(s.take(s.len() as int - 1) =~= a.take(i));
    assert(s[s.len() as int - 1] == a[i]);
}

proof fn count_negative_step(a: Seq<int>, i: int)
    requires 0 <= i < a.len()
    ensures
        count_negative(a.take(i + 1)) == count_negative(a.take(i))
            + if a[i] < 0 { 1 as int } else { 0 as int }
{
    assert(a.take(i + 1) =~= a.take(i).push(a[i]));
    let s = a.take(i + 1);
    assert(s.len() == i + 1);
    assert(s.take(s.len() as int - 1) =~= a.take(i));
    assert(s[s.len() as int - 1] == a[i]);
}

fn be_positive(a: &Vec<i64>) -> (d: i64)
    requires a@.len() < usize::MAX
    ensures
        d != 0 ==> -1000 <= d <= 1000
            && count_positive_after_div(vec_to_spec(a@), d as int) >= ceil_half(a@.len() as int),
        d == 0 ==> (forall|d_prime: int| d_prime == 0 || #[trigger] cpd(vec_to_spec(a@), d_prime) < ceil_half(a@.len() as int)),
{
    let ghost a_spec: Seq<int> = vec_to_spec(a@);
    let n: usize = a.len();
    let mut pcount: usize = 0;
    let mut ncount: usize = 0;
    let mut i: usize = 0;

    proof {
        assert(a_spec.take(0int) =~= Seq::<int>::empty());
    }

    while i < n
        invariant
            0 <= i <= n,
            n == a.len(),
            n < usize::MAX,
            a_spec =~= vec_to_spec(a@),
            pcount as int == count_positive(a_spec.take(i as int)),
            ncount as int == count_negative(a_spec.take(i as int)),
            pcount <= i,
            ncount <= i,
        decreases n - i,
    {
        proof {
            vec_to_spec_index(a@, i as int);
            count_positive_step(a_spec, i as int);
            count_negative_step(a_spec, i as int);
        }
        let ai = a[i];
        if ai > 0 {
            pcount = pcount + 1;
        } else if ai < 0 {
            ncount = ncount + 1;
        }
        i = i + 1;
    }

    proof {
        assert(a_spec.take(n as int) =~= a_spec);
    }

    let half: usize = (n + 1) / 2;

    if pcount >= half {
        proof {
            count_pos_div_pos(a_spec, 1);
        }
        1
    } else if ncount >= half {
        proof {
            count_pos_div_neg(a_spec, -1);
        }
        -1
    } else {
        proof {
            assert forall|d_prime: int| d_prime != 0 implies #[trigger] cpd(a_spec, d_prime) < ceil_half(a_spec.len() as int) by {
                if d_prime > 0 {
                    count_pos_div_pos(a_spec, d_prime);
                } else {
                    count_pos_div_neg(a_spec, d_prime);
                }
            }
        }
        0
    }
}

fn main() {}

} // verus!

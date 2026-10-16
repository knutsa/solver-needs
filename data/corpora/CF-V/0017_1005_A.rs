use vstd::prelude::*;

verus! {

// ghost function CountingSeq(n: int): seq<int>
spec fn CountingSeq(n: int) -> Seq<int>
    decreases n
{
    if n <= 0 { Seq::empty() } else { CountingSeq(n - 1).push(n) }
}

// ghost predicate AllPositive(s: seq<int>)
spec fn AllPositive(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> #[trigger] s[i] >= 1
}

// ghost function ConcatStairways(stairs: seq<int>): seq<int>
spec fn ConcatStairways(stairs: Seq<int>) -> Seq<int>
    decreases stairs.len()
{
    if stairs.len() == 0 {
        Seq::empty()
    } else {
        ConcatStairways(stairs.take(stairs.len() - 1)).add(
            CountingSeq(stairs[stairs.len() - 1])
        )
    }
}

// ghost predicate IsValidInput(a: seq<int>)
spec fn IsValidInput(a: Seq<int>) -> bool {
    a.len() >= 1 &&
    a[0] == 1 &&
    forall|i: int| 1 <= i < a.len() ==> (#[trigger] a[i] == 1 || a[i] == a[i - 1] + 1)
}

// Lemma: CountingSeq(1) == [1]
proof fn lemma_counting_seq_one()
    ensures CountingSeq(1) =~= seq![1int],
{
    reveal_with_fuel(CountingSeq, 2);
}

// Helper lemma: ConcatStairways(stairs ++ [cnt]) == ConcatStairways(stairs) ++ CountingSeq(cnt)
proof fn lemma_concat_stairways_snoc(stairs: Seq<int>, cnt: int)
    ensures
        ConcatStairways(stairs.push(cnt)) =~= ConcatStairways(stairs).add(CountingSeq(cnt)),
{
    let s = stairs.push(cnt);
    assert(s.take(s.len() - 1) =~= stairs);
}

// Helper: AllPositive is preserved when appending a positive element
proof fn lemma_all_positive_push(stairs: Seq<int>, v: int)
    requires
        AllPositive(stairs),
        v >= 1,
    ensures
        AllPositive(stairs.push(v)),
{
    let s = stairs.push(v);
    assert forall|i: int| 0 <= i < s.len() implies #[trigger] s[i] >= 1 by {
        if i < stairs.len() {
            assert(s[i] == stairs[i]);
        }
    }
}

// Lemma: a.take(i).push(a[i]) == a.take(i+1)
proof fn lemma_take_push(a: Seq<int>, i: int)
    requires 0 <= i < a.len(),
    ensures a.take(i).push(a[i]) =~= a.take(i + 1),
{
}

// Lemma for the new stairway case
proof fn lemma_new_stairway(stairs: Seq<int>, cnt: int, a: Seq<int>, i: int)
    requires
        0 < i < a.len(),
        cnt >= 1,
        ConcatStairways(stairs).add(CountingSeq(cnt)) =~= a.take(i),
        a[i] == 1,
    ensures
        ConcatStairways(stairs.push(cnt)).add(CountingSeq(1)) =~= a.take(i + 1),
{
    lemma_concat_stairways_snoc(stairs, cnt);
    lemma_counting_seq_one();
    lemma_take_push(a, i);
    assert(a.take(i).add(seq![1int]) =~= a.take(i).push(1));
}

// Lemma for the continue stairway case
proof fn lemma_continue_stairway(stairs: Seq<int>, cnt: int, a: Seq<int>, i: int)
    requires
        0 < i < a.len(),
        cnt >= 1,
        cnt == a[i - 1],
        ConcatStairways(stairs).add(CountingSeq(cnt)) =~= a.take(i),
        a[i] == cnt + 1,
    ensures
        ConcatStairways(stairs).add(CountingSeq(cnt + 1)) =~= a.take(i + 1),
{
    // CountingSeq(cnt + 1) == CountingSeq(cnt).push(cnt + 1) by def since cnt+1 > 0
    assert(CountingSeq(cnt + 1) =~= CountingSeq(cnt).push(cnt + 1));
    lemma_take_push(a, i);
    let prefix = ConcatStairways(stairs);
    let cs = CountingSeq(cnt);
    assert(prefix.add(cs.push(cnt + 1)) =~= prefix.add(cs).push(cnt + 1));
}

// Lemma: initial step
proof fn lemma_initial_step(a: Seq<int>)
    requires a.len() >= 1, a[0] == 1,
    ensures
        ConcatStairways(Seq::<int>::empty()).add(CountingSeq(1)) =~= a.take(1int),
{
    lemma_counting_seq_one();
    assert(ConcatStairways(Seq::<int>::empty()) =~= Seq::<int>::empty());
    assert(Seq::<int>::empty().add(seq![1int]) =~= seq![1int]);
    assert(a.take(1int) =~= seq![a[0]]);
}

// Lemma: map_values distributes over push
proof fn lemma_map_push(v: Seq<i64>, x: i64)
    ensures
        v.push(x).map_values(|y: i64| y as int) =~= v.map_values(|y: i64| y as int).push(x as int),
{
    let lhs = v.push(x).map_values(|y: i64| y as int);
    let rhs = v.map_values(|y: i64| y as int).push(x as int);
    assert(lhs.len() == rhs.len());
    assert forall|i: int| 0 <= i < lhs.len() implies lhs[i] == rhs[i] by {
        if i < v.len() as int {
            assert(lhs[i] == (v[i] as int));
            assert(rhs[i] == (v[i] as int));
        }
    }
}

// Helper: establish that a_spec[idx] < i64::MAX from the raw precondition
proof fn lemma_cnt_bound(a: Seq<i64>, a_spec: Seq<int>, idx: int)
    requires
        a_spec =~= a.map_values(|x: i64| x as int),
        0 <= idx < a.len(),
        forall|k: int| 0 <= k < a.len() ==> 0 <= #[trigger] a[k] < i64::MAX,
    ensures
        a_spec[idx] < i64::MAX,
        a_spec[idx] >= 0,
{
    assert(a[idx] < i64::MAX);
    assert(a[idx] >= 0);
    assert(a_spec[idx] == a[idx] as int);
}

#[verifier::loop_isolation(false)]
fn TanyaAndStairways(a: &Vec<i64>) -> (result: (usize, Vec<i64>))
    requires
        IsValidInput(a@.map_values(|x: i64| x as int)),
        a@.len() < usize::MAX,
        forall|k: int| 0 <= k < a@.len() ==> 0 <= #[trigger] a@[k] < i64::MAX,
    ensures
        result.0 as int == result.1@.len(),
        result.0 >= 1,
        AllPositive(result.1@.map_values(|x: i64| x as int)),
        ConcatStairways(result.1@.map_values(|x: i64| x as int))
            =~= a@.map_values(|x: i64| x as int),
{
    let ghost a_spec: Seq<int> = a@.map_values(|x: i64| x as int);
    let mut stairs: Vec<i64> = Vec::new();
    let mut cnt: i64 = 0;

    for idx in 0..a.len()
        invariant
            a_spec =~= a@.map_values(|x: i64| x as int),
            a@.len() < usize::MAX,
            forall|k: int| 0 <= k < a@.len() ==> 0 <= #[trigger] a@[k] < i64::MAX,
            IsValidInput(a_spec),
            idx == 0 ==> cnt == 0 && stairs@.len() == 0,
            idx > 0 ==> cnt as int == a_spec[idx as int - 1] && cnt >= 1,
            AllPositive(stairs@.map_values(|x: i64| x as int)),
            ConcatStairways(stairs@.map_values(|x: i64| x as int)).add(
                CountingSeq(cnt as int)
            ) =~= a_spec.take(idx as int),
            0 <= cnt < i64::MAX,
            stairs@.len() <= idx as int,
    {
        let ghost stairs_spec = stairs@.map_values(|x: i64| x as int);
        if idx == 0 {
            cnt = 1;
            proof {
                lemma_initial_step(a_spec);
            }
        } else if a[idx] == 1 {
            proof {
                lemma_all_positive_push(stairs_spec, cnt as int);
                lemma_new_stairway(stairs_spec, cnt as int, a_spec, idx as int);
                lemma_map_push(stairs@, cnt);
                // Explicitly establish cnt bound for new cnt=1
                assert(1i64 >= 0);
                assert((1i64 as int) < i64::MAX);
            }
            stairs.push(cnt);
            cnt = 1;
        } else {
            proof {
                // Explicitly establish that a[idx] is in range, so cnt+1 < i64::MAX
                lemma_cnt_bound(a@, a_spec, idx as int);
                // a[idx] == a[idx-1] + 1 == cnt + 1 from IsValidInput
                assert(a_spec[idx as int] == a_spec[idx as int - 1] + 1);
                assert(cnt as int == a_spec[idx as int - 1]);
                assert(cnt as int + 1 == a_spec[idx as int]);
                assert(a_spec[idx as int] < i64::MAX);
                assert(cnt + 1 < i64::MAX);
                lemma_continue_stairway(stairs_spec, cnt as int, a_spec, idx as int);
            }
            cnt = cnt + 1;
        }
    }

    proof {
        assert(a_spec.take(a_spec.len() as int) =~= a_spec);
        lemma_concat_stairways_snoc(
            stairs@.map_values(|x: i64| x as int), cnt as int,
        );
        lemma_all_positive_push(stairs@.map_values(|x: i64| x as int), cnt as int);
        lemma_map_push(stairs@, cnt);
    }

    stairs.push(cnt);
    let t: usize = stairs.len();
    (t, stairs)
}

fn main() {}

} // verus!

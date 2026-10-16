use vstd::prelude::*;

verus! {

spec fn all_consider_easy(opinions: Seq<int>) -> bool {
    forall|i: int| 0 <= i < opinions.len() ==> #[trigger] opinions[i] == 0
}

#[verifier::loop_isolation(false)]
fn is_easy_problem(_n: i64, opinions: &Vec<i64>) -> (result: bool)
    ensures
        all_consider_easy(opinions@.map_values(|x: i64| x as int)) ==> result == true,
        !all_consider_easy(opinions@.map_values(|x: i64| x as int)) ==> result == false,
{
    let mut all_zero: bool = true;
    let mut i: usize = 0;
    while i < opinions.len()
        invariant
            0 <= i <= opinions.len(),
            all_zero <==> all_consider_easy(opinions@.map_values(|x: i64| x as int).take(i as int)),
        decreases opinions.len() - i,
    {
        if opinions[i] != 0 {
            all_zero = false;
            proof {
                let mapped = opinions@.map_values(|x: i64| x as int);
                assert(mapped[i as int] == opinions@[i as int] as int);
                assert(mapped.take((i as int) + 1)[i as int] == mapped[i as int]);
                assert(mapped.take((i as int) + 1)[i as int] != 0);
            }
        }
        proof {
            assert(opinions@.map_values(|x: i64| x as int).take((i as int) + 1).drop_last()
                =~= opinions@.map_values(|x: i64| x as int).take(i as int));
        }
        i = i + 1;
    }
    proof {
        assert(opinions@.map_values(|x: i64| x as int).take(opinions.len() as int)
            =~= opinions@.map_values(|x: i64| x as int));
    }
    all_zero
}

fn main() {}

} // verus!
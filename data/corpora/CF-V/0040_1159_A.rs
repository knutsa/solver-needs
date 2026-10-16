use vstd::prelude::*;

verus! {

spec fn delta(c: char) -> int {
    if c == '-' { -1int } else { 1int }
}

spec fn sum_deltas(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0int
    } else {
        sum_deltas(s.take(s.len() - 1)) + delta(s[s.len() - 1])
    }
}

proof fn sum_deltas_append(s: Seq<char>, c: char)
    ensures sum_deltas(s.push(c)) == sum_deltas(s) + delta(c)
{
    let t = s.push(c);
    assert(t.len() == s.len() + 1);
    assert(t[t.len() - 1] == c);
    assert(t.take(t.len() - 1) =~= s);
}

spec fn valid_execution(s: Seq<char>, init: int) -> bool {
    init >= 0 &&
    forall|k: int| 0 <= k <= s.len() ==> init + sum_deltas(s.take(k)) >= 0
}

spec fn final_pile_size(s: Seq<char>, init: int) -> int {
    init + sum_deltas(s)
}

#[verifier::loop_isolation(false)]
fn pile_of_stones(s: &Vec<char>) -> (result: i64)
    requires s@.len() <= i64::MAX as int,
    ensures
        exists|init: int| init >= 0 && valid_execution(s@, init) && final_pile_size(s@, init) == result as int,
        forall|init: int| valid_execution(s@, init) ==> final_pile_size(s@, init) >= result as int,
{
    let mut result: i64 = 0;
    let mut i: usize = 0;
    let ghost mut absorbed: int = 0;
    let ghost mut min_k: int = 0;

    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            result >= 0,
            absorbed >= 0,
            result == absorbed + sum_deltas(s@.take(i as int)),
            forall|k: int| 0 <= k <= i ==> absorbed + sum_deltas(s@.take(k)) >= 0,
            0 <= min_k <= i,
            sum_deltas(s@.take(min_k)) == -absorbed,
            result <= i as i64,
            absorbed <= i as int,
            s@.len() <= i64::MAX as int,
        decreases s.len() - i
    {
        // Key lemma: s@.take(i+1) == s@.take(i).push(s@[i])
        proof {
            let si = s@.take(i as int);
            let si1 = s@.take(i as int + 1);
            assert(si1 =~= si.push(s@[i as int]));
            sum_deltas_append(si, s@[i as int]);
        }

        if s[i] == '-' {
            if result > 0 {
                result = result - 1;
            } else {
                proof { absorbed = absorbed + 1; }
                proof { min_k = i as int + 1; }
            }
        } else {
            result = result + 1;
        }
        i = i + 1;
    }

    proof {
        // s@.take(s@.len()) == s@
        assert(s@.take(s@.len() as int) =~= s@);

        // Witness for first postcondition
        assert(valid_execution(s@, absorbed));
        assert(final_pile_size(s@, absorbed) == result as int);

        // Second postcondition: minimality
        // For any valid init, init + sum_deltas(s@.take(min_k)) >= 0
        // so init >= -sum_deltas(s@.take(min_k)) == absorbed
        // so init + sum_deltas(s@) >= absorbed + sum_deltas(s@) == result
        assert forall|init: int| valid_execution(s@, init) implies final_pile_size(s@, init) >= result as int by {
            assert(0 <= min_k <= s@.len() as int);
            assert(init + sum_deltas(s@.take(min_k)) >= 0);
            assert(init >= absorbed);
        }
    }

    result
}

fn main() {}

} // verus!

use vstd::prelude::*;

verus! {

// Count the number of 'a' characters in a sequence (string represented as Seq<char>)
pub open spec fn count_a(s: Seq<char>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[s.len() - 1] == 'a' { 1int } else { 0int }) + count_a(s.take(s.len() as int - 1))
    }
}

// Helper to check if a specific num_a witnesses a good subsequence
pub open spec fn good_witness(s: Seq<char>, len: int, num_a: int) -> bool {
    0 <= num_a <= len
    && num_a <= count_a(s)
    && (len - num_a + count_a(s) <= s.len())
    && 2 * num_a > len
}

// Can we form a "good" subsequence of exactly `len` characters from `s`?
pub open spec fn can_form_good_of_length(s: Seq<char>, len: int) -> bool {
    0 <= len <= s.len()
    && exists|num_a: int| #[trigger] good_witness(s, len, num_a)
}

proof fn count_a_bound(s: Seq<char>)
    ensures count_a(s) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        count_a_bound(s.take(s.len() as int - 1));
    }
}

proof fn count_a_nonneg(s: Seq<char>)
    ensures count_a(s) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        count_a_nonneg(s.take(s.len() as int - 1));
    }
}

fn love_a(s: &Vec<char>) -> (result: usize)
    requires
        count_a(s@) >= 1,
        s.len() < usize::MAX / 2,
    ensures
        0 <= result <= s.len(),
        can_form_good_of_length(s@, result as int),
        forall|k: int| (result < k && k <= s@.len()) ==> !can_form_good_of_length(s@, k),
{
    proof {
        count_a_bound(s@);
        count_a_nonneg(s@);
    }

    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            count == count_a(s@.take(i as int)),
            count <= i,
            s.len() < usize::MAX / 2,
        decreases s.len() - i,
    {
        proof {
            assert(s@.take(i as int + 1).drop_last() =~= s@.take(i as int));
            count_a_bound(s@.take(i as int + 1));
        }
        if s[i] == 'a' {
            count = count + 1;
        }
        i = i + 1;
    }

    proof {
        assert(s@.take(s@.len() as int) =~= s@);
    }

    // count == count_a(s@), and count_a(s@) >= 1, so count >= 1
    // Also count <= s.len() < usize::MAX / 2, so 2 * count won't overflow
    let candidate: usize = 2 * count - 1;
    if s.len() < candidate {
        let result = s.len();
        proof {
            // Witness for can_form_good_of_length: num_a = count
            assert(good_witness(s@, s@.len() as int, count as int));
        }
        result
    } else {
        let result = candidate;
        proof {
            // Witness for can_form_good_of_length: num_a = count
            assert(good_witness(s@, candidate as int, count as int));
        }

        proof {
            // Prove maximality
            assert forall|k: int| (k > candidate as int && k <= s@.len()) implies !can_form_good_of_length(s@, k) by {
                assert(k >= 2 * (count as int));
                assert forall|num_a: int| #[trigger] good_witness(s@, k, num_a) implies false by {
                    // good_witness requires num_a <= count_a(s@) = count and 2*num_a > k >= 2*count
                    // contradiction: 2*num_a > 2*count but num_a <= count
                };
            };
        }
        result
    }
}

fn main() {}

} // verus!

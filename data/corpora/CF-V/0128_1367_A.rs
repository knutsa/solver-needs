use vstd::prelude::*;

verus! {

spec fn bob_encode(a: Seq<char>) -> Seq<char>
    recommends a.len() >= 2
    decreases a.len()
{
    if a.len() <= 2 {
        a
    } else {
        a.subrange(0, 2) + bob_encode(a.subrange(1, a.len() as int))
    }
}

proof fn bob_encode_inverse(a: Seq<char>, b: Seq<char>)
    requires
        a.len() >= 2,
        b.len() == 2 * (a.len() - 1),
        a[0] == b[0],
        forall|j: int| 1 <= j < a.len() ==> (#[trigger] a[j]) == b[2 * j - 1],
        forall|k: int| 1 <= k < a.len() - 1 ==> (#[trigger] b[2 * k]) == b[2 * k - 1],
    ensures
        bob_encode(a) == b,
    decreases a.len()
{
    if a.len() == 2 {
        assert(a[1] == b[1]);
        assert(a =~= b);
    } else {
        let a_prime = a.subrange(1, a.len() as int);
        let b_prime = b.subrange(2, b.len() as int);

        // a'[0] == b'[0] via overlap
        assert(a[1] == b[1]);
        assert(b[2] == b[1]);
        assert(a_prime[0] == b_prime[0]);

        // Index mapping for recursive call
        assert forall|j: int| 1 <= j < a_prime.len() implies (#[trigger] a_prime[j]) == b_prime[2 * j - 1] by {
            assert(a_prime[j] == a[j + 1]);
            assert(a[j + 1] == b[2 * (j + 1) - 1]);
            assert(b_prime[2 * j - 1] == b[2 * j + 1]);
        };

        // Overlap property for b'
        assert forall|k: int| 1 <= k < a_prime.len() - 1 implies (#[trigger] b_prime[2 * k]) == b_prime[2 * k - 1] by {
            assert(b_prime[2 * k] == b[2 * (k + 1)]);
            assert(b_prime[2 * k - 1] == b[2 * (k + 1) - 1]);
        };

        bob_encode_inverse(a_prime, b_prime);

        assert(a.subrange(0, 2) =~= seq![a[0], a[1]]);
        assert(b.subrange(0, 2) =~= seq![b[0], b[1]]);
        assert(b =~= b.subrange(0, 2) + b.subrange(2, b.len() as int));
    }
}

#[verifier::loop_isolation(false)]
fn short_substrings(b: &Vec<char>) -> (a: Vec<char>)
    requires
        b@.len() >= 2,
        b@.len() % 2 == 0,
        b@.len() + 2 <= usize::MAX,
        forall|k: int| 1 <= k < b@.len() / 2 ==> (#[trigger] b@[2 * k]) == b@[2 * k - 1],
    ensures
        a@.len() >= 2,
        bob_encode(a@) == b@,
{
    let mut partial: Vec<char> = Vec::new();
    let ghost blen = b@.len();
    let mut idx: usize = 0;
    while idx < b.len() / 2
        invariant
            0 <= idx as int <= blen / 2,
            partial@.len() == idx as int,
            forall|j: int| 0 <= j < partial@.len() ==> (#[trigger] partial@[j]) == b@[2 * j + 1],
            blen == b@.len(),
            b@.len() >= 2,
            b@.len() % 2 == 0,
            b@.len() + 2 <= usize::MAX,
        decreases blen / 2 - idx as int,
    {
        let i = 2 * idx + 1;
        partial.push(b[i]);
        idx = idx + 1;
    }

    let mut a: Vec<char> = Vec::new();
    a.push(b[0]);
    let mut j: usize = 0;
    while j < partial.len()
        invariant
            0 <= j <= partial@.len(),
            a@.len() == j as int + 1,
            a@[0] == b@[0],
            forall|k: int| 0 <= k < j as int ==> a@[k + 1] == (#[trigger] partial@[k]),
        decreases partial@.len() - j,
    {
        a.push(partial[j]);
        j += 1;
    }

    proof {
        assert(partial@.len() == b@.len() / 2);
        assert(a@.len() == partial@.len() + 1);
        assert(b@.len() == 2 * (a@.len() - 1));

        assert forall|j: int| 1 <= j < a@.len() implies (#[trigger] a@[j]) == b@[2 * j - 1] by {
            assert(a@[j] == partial@[j - 1]);
            assert(partial@[j - 1] == b@[2 * (j - 1) + 1]);
        };

        bob_encode_inverse(a@, b@);
    }

    a
}

fn main() {}

} // verus!

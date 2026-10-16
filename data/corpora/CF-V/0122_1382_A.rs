use vstd::prelude::*;

verus! {

spec fn vec_to_spec(v: Seq<i64>) -> Seq<int> {
    v.map(|_idx, x: i64| x as int)
}

spec fn is_subsequence(c: Seq<int>, s: Seq<int>) -> bool
    decreases s.len(),
{
    if c.len() == 0 {
        true
    } else if s.len() == 0 {
        false
    } else if c[c.len() - 1] == s[s.len() - 1] {
        is_subsequence(c.take(c.len() as int - 1), s.take(s.len() as int - 1))
    } else {
        is_subsequence(c, s.take(s.len() as int - 1))
    }
}

spec fn exists_common_subseq_of_len(a: Seq<int>, b: Seq<int>, k: nat) -> bool
    decreases a.len() + b.len(),
{
    if k == 0 {
        true
    } else if a.len() == 0 || b.len() == 0 {
        false
    } else if a[a.len() - 1] == b[b.len() - 1] {
        exists_common_subseq_of_len(a.take(a.len() as int - 1), b.take(b.len() as int - 1), (k - 1) as nat)
        || exists_common_subseq_of_len(a.take(a.len() as int - 1), b, k)
        || exists_common_subseq_of_len(a, b.take(b.len() as int - 1), k)
    } else {
        exists_common_subseq_of_len(a.take(a.len() as int - 1), b, k)
        || exists_common_subseq_of_len(a, b.take(b.len() as int - 1), k)
    }
}

spec fn min_nat(x: nat, y: nat) -> nat {
    if x <= y { x } else { y }
}

spec fn no_common_elements(a: Seq<int>, b: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] != b[j]
}

proof fn singleton_is_subsequence(x: int, s: Seq<int>, idx: int)
    requires
        0 <= idx < s.len(),
        s[idx] == x,
    ensures
        is_subsequence(seq![x], s),
    decreases s.len(),
{
    let sx = seq![x];
    reveal_with_fuel(is_subsequence, 2);
    if x == s[s.len() - 1] {
        assert(sx[sx.len() - 1] == s[s.len() - 1]);
        assert(sx.take(sx.len() as int - 1) =~= Seq::<int>::empty());
        assert(is_subsequence(Seq::<int>::empty(), s.take(s.len() as int - 1)));
    } else {
        assert(idx < s.len() - 1);
        assert(s.take(s.len() as int - 1)[idx] == x);
        singleton_is_subsequence(x, s.take(s.len() as int - 1), idx);
    }
}

proof fn no_common_elements_means_no_common_subseq(a: Seq<int>, b: Seq<int>, k: nat)
    requires
        k >= 1,
        no_common_elements(a, b),
    ensures
        !exists_common_subseq_of_len(a, b, k),
    decreases a.len() + b.len(),
{
    if a.len() == 0 || b.len() == 0 {
    } else {
        assert(a[a.len() - 1] != b[b.len() - 1]);

        assert(no_common_elements(a.take(a.len() as int - 1), b)) by {
            assert forall|i: int, j: int|
                0 <= i < a.take(a.len() as int - 1).len() && 0 <= j < b.len()
                implies #[trigger] a.take(a.len() as int - 1)[i] != #[trigger] b[j]
            by {
                assert(a.take(a.len() as int - 1)[i] == a[i]);
            }
        }
        no_common_elements_means_no_common_subseq(a.take(a.len() as int - 1), b, k);

        assert(no_common_elements(a, b.take(b.len() as int - 1))) by {
            assert forall|i: int, j: int|
                0 <= i < a.len() && 0 <= j < b.take(b.len() as int - 1).len()
                implies #[trigger] a[i] != #[trigger] b.take(b.len() as int - 1)[j]
            by {
                assert(b.take(b.len() as int - 1)[j] == b[j]);
            }
        }
        no_common_elements_means_no_common_subseq(a, b.take(b.len() as int - 1), k);
    }
}

fn common_subsequence(a: &Vec<i64>, b: &Vec<i64>) -> (result: (bool, Vec<i64>))
    ensures
        ({
            let (found, c) = result;
            let a_spec = vec_to_spec(a@);
            let b_spec = vec_to_spec(b@);
            let c_spec = vec_to_spec(c@);
            if found {
                c_spec.len() >= 1
                && is_subsequence(c_spec, a_spec)
                && is_subsequence(c_spec, b_spec)
            } else {
                forall|len: nat| #![trigger exists_common_subseq_of_len(a_spec, b_spec, len)]
                    1 <= len <= min_nat(a_spec.len() as nat, b_spec.len() as nat)
                    ==> !exists_common_subseq_of_len(a_spec, b_spec, len)
            }
        }),
{
    let a_spec: Ghost<Seq<int>> = Ghost(vec_to_spec(a@));
    let b_spec: Ghost<Seq<int>> = Ghost(vec_to_spec(b@));

    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            a_spec@ == vec_to_spec(a@),
            b_spec@ == vec_to_spec(b@),
            forall|i2: int, j: int|
                0 <= i2 < i as int && 0 <= j < b_spec@.len()
                ==> a_spec@[i2] != b_spec@[j],
        decreases a.len() - i,
    {
        let mut j: usize = 0;
        while j < b.len()
            invariant
                0 <= i < a.len(),
                0 <= j <= b.len(),
                a_spec@ == vec_to_spec(a@),
                b_spec@ == vec_to_spec(b@),
                forall|j2: int| 0 <= j2 < j as int ==> a_spec@[i as int] != b_spec@[j2],
                forall|i2: int, j2: int|
                    0 <= i2 < i as int && 0 <= j2 < b_spec@.len()
                    ==> a_spec@[i2] != b_spec@[j2],
            decreases b.len() - j,
        {
            if a[i] == b[j] {
                let val = a[i];
                let c: Vec<i64> = vec![val];
                proof {
                    let c_spec = vec_to_spec(c@);
                    assert(c_spec =~= seq![val as int]);
                    singleton_is_subsequence(val as int, a_spec@, i as int);
                    singleton_is_subsequence(val as int, b_spec@, j as int);
                }
                return (true, c);
            }
            j = j + 1;
        }
        i = i + 1;
    }

    proof {
        assert(no_common_elements(a_spec@, b_spec@));
        assert forall|len: nat|
            1 <= len <= min_nat(a_spec@.len() as nat, b_spec@.len() as nat)
            implies !#[trigger] exists_common_subseq_of_len(a_spec@, b_spec@, len)
        by {
            no_common_elements_means_no_common_subseq(a_spec@, b_spec@, len);
        }
    }
    (false, Vec::new())
}

fn main() {}

} // verus!

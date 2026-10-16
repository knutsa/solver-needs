use vstd::prelude::*;

verus! {

spec fn TrailingParens(s: Seq<u8>) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else if s[s.len() - 1] == 41u8 {
        1 + TrailingParens(s.take(s.len() - 1))
    } else {
        0nat
    }
}

spec fn IsBad(s: Seq<u8>) -> bool
{
    TrailingParens(s) > s.len() - TrailingParens(s)
}

#[verifier::loop_isolation(false)]
fn InGameChat(s: &Vec<u8>) -> (bad: bool)
    ensures bad == IsBad(s@)
{
    let n: usize = s.len();
    let mut trailing: usize = 0;
    proof {
        assert(s@.take(n as int) =~= s@);
    }
    while trailing < n && s[n - 1 - trailing] == 41u8
        invariant
            trailing <= n,
            n == s@.len(),
            TrailingParens(s@) == trailing as nat + TrailingParens(s@.take((n - trailing) as int)),
        decreases n - trailing
    {
        proof {
            assert(s@.take((n - trailing) as int).drop_last() =~= s@.take((n - trailing - 1) as int));
        }
        trailing += 1;
    }
    proof {
        assert(TrailingParens(s@.take((n - trailing) as int)) == 0nat);
    }
    let bad = trailing > n - trailing;
    bad
}

fn main() {}

} // verus!
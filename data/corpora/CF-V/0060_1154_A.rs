use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::multiset::*;

verus! {

// Ghost function: remove element at index m from sequence
spec fn remove_index(s: Seq<int>, m: int) -> Seq<int>
    recommends 0 <= m < s.len()
{
    s.subrange(0, m).add(s.subrange(m + 1, s.len() as int))
}

// Build multiset from the four candidate sums
spec fn four_multiset(a: int, b: int, c: int) -> Multiset<int>
{
    Multiset::empty().insert(a + b).insert(a + c).insert(b + c).insert(a + b + c)
}

// Core postcondition
spec fn is_valid_restoration(x: Seq<int>, a: int, b: int, c: int) -> bool
{
    x.len() == 4
    && a > 0 && b > 0 && c > 0
    && four_multiset(a, b, c) =~= x.to_multiset()
}

// Check whether choosing index m yields valid a, b, c
spec fn check_index(x: Seq<int>, m: int) -> bool
    recommends x.len() == 4 && 0 <= m < 4
{
    let rest = remove_index(x, m);
    let a = x[m] - rest[0];
    let b = x[m] - rest[1];
    let c = x[m] - rest[2];
    a > 0 && b > 0 && c > 0
    && four_multiset(a, b, c) =~= x.to_multiset()
}

// Compilable precondition: there exists a valid index
spec fn has_valid_restoration(x: Seq<int>) -> bool
    recommends x.len() == 4
{
    exists|m: int| 0 <= m < 4 && check_index(x, m)
}

// Lemma: existential implies one of the four concrete indices works
proof fn has_valid_means_one_works(x: Seq<int>)
    requires x.len() == 4, has_valid_restoration(x)
    ensures check_index(x, 0) || check_index(x, 1) || check_index(x, 2) || check_index(x, 3)
{
    let m = choose|m: int| 0 <= m < 4 && check_index(x, m);
    assert(0 <= m < 4);
}

// Lemma: concrete remove_index values for length-4 sequences
proof fn remove_index_concrete(x: Seq<int>)
    requires x.len() == 4
    ensures
        remove_index(x, 0) =~= seq![x[1], x[2], x[3]],
        remove_index(x, 1) =~= seq![x[0], x[2], x[3]],
        remove_index(x, 2) =~= seq![x[0], x[1], x[3]],
        remove_index(x, 3) =~= seq![x[0], x[1], x[2]],
{
}

// Proof function that mirrors the Dafny method logic
proof fn restore_three_numbers(x: Seq<int>) -> (result: (int, int, int))
    requires x.len() == 4, has_valid_restoration(x)
    ensures is_valid_restoration(x, result.0, result.1, result.2)
{
    has_valid_means_one_works(x);
    remove_index_concrete(x);

    // Try m=0
    let a0 = x[0] - x[1];
    let b0 = x[0] - x[2];
    let c0 = x[0] - x[3];
    if a0 > 0 && b0 > 0 && c0 > 0 && four_multiset(a0, b0, c0) =~= x.to_multiset() {
        return (a0, b0, c0);
    }

    // Try m=1
    let a1 = x[1] - x[0];
    let b1 = x[1] - x[2];
    let c1 = x[1] - x[3];
    if a1 > 0 && b1 > 0 && c1 > 0 && four_multiset(a1, b1, c1) =~= x.to_multiset() {
        return (a1, b1, c1);
    }

    // Try m=2
    let a2 = x[2] - x[0];
    let b2 = x[2] - x[1];
    let c2 = x[2] - x[3];
    if a2 > 0 && b2 > 0 && c2 > 0 && four_multiset(a2, b2, c2) =~= x.to_multiset() {
        return (a2, b2, c2);
    }

    // m=3 must work
    let a3 = x[3] - x[0];
    let b3 = x[3] - x[1];
    let c3 = x[3] - x[2];
    assert(check_index(x, 3));
    (a3, b3, c3)
}

fn main() {}

} // verus!

use vstd::prelude::*;

verus! {

// ghost function DotProduct
spec fn dot_product(a: Seq<int>, b: Seq<int>) -> int
    decreases a.len(),
{
    if a.len() == 0 || b.len() == 0 {
        0
    } else {
        dot_product(a.take(a.len() as int - 1), b.take(b.len() as int - 1))
            + a[a.len() as int - 1] * b[b.len() as int - 1]
    }
}

// ghost predicate AllNonZero
spec fn all_non_zero(s: Seq<int>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] != 0
}

// ghost predicate AllBounded
spec fn all_bounded(s: Seq<int>, bound: int) -> bool {
    forall|i: int| 0 <= i < s.len() ==> -bound <= s[i] && s[i] <= bound
}

// ghost predicate ValidSolution
spec fn valid_solution(a: Seq<int>, b: Seq<int>) -> bool {
    a.len() == b.len()
        && all_non_zero(b)
        && all_bounded(b, 100)
        && dot_product(a, b) == 0
}

// Helper lemma: pushing preserves all_non_zero
proof fn push_preserves_non_zero(s: Seq<int>, v: int)
    requires
        all_non_zero(s),
        v != 0,
    ensures
        all_non_zero(s.push(v)),
{
    assert forall|i: int| 0 <= i < s.push(v).len() implies s.push(v)[i] != 0 by {
        if i < s.len() {
            assert(s.push(v)[i] == s[i]);
        } else {
            assert(s.push(v)[i] == v);
        }
    }
}

// Helper lemma: pushing preserves all_bounded
proof fn push_preserves_bounded(s: Seq<int>, v: int, bound: int)
    requires
        all_bounded(s, bound),
        -bound <= v && v <= bound,
    ensures
        all_bounded(s.push(v), bound),
{
    assert forall|i: int| 0 <= i < s.push(v).len() implies (-bound <= s.push(v)[i] && s.push(v)[i] <= bound) by {
        if i < s.len() {
            assert(s.push(v)[i] == s[i]);
        } else {
            assert(s.push(v)[i] == v);
        }
    }
}

// lemma DotProductAppend
proof fn dot_product_append(a: Seq<int>, b: Seq<int>, x: int, y: int)
    requires
        a.len() == b.len(),
    ensures
        dot_product(a.push(x), b.push(y)) == dot_product(a, b) + x * y,
{
    let a_prime = a.push(x);
    let b_prime = b.push(y);
    assert(a_prime.take(a_prime.len() as int - 1) =~= a);
    assert(b_prime.take(b_prime.len() as int - 1) =~= b);
}

// Recursive proof fn replacing the loop
proof fn find_sasuke_rec(a: Seq<int>, i: int, b: Seq<int>) -> (result: Seq<int>)
    requires
        a.len() % 2 == 0,
        all_non_zero(a),
        all_bounded(a, 100),
        0 <= i <= a.len(),
        i % 2 == 0,
        b.len() == i,
        all_non_zero(b),
        all_bounded(b, 100),
        dot_product(a.take(i), b) == 0,
    ensures
        result.len() == a.len(),
        all_non_zero(result),
        all_bounded(result, 100),
        dot_product(a, result) == 0,
    decreases a.len() - i,
{
    if i >= a.len() {
        assert(a.take(a.len() as int) =~= a);
        b
    } else {
        // Even step: push a[i+1]
        let val1 = a[i + 1];
        dot_product_append(a.take(i), b, a[i], val1);
        assert(a.take(i).push(a[i]) =~= a.take(i + 1));
        push_preserves_non_zero(b, val1);
        push_preserves_bounded(b, val1, 100);
        let b1 = b.push(val1);
        // Now: dot_product(a.take(i+1), b1) == a[i] * a[i+1]

        // Odd step: push -a[i]
        let val2 = -a[i];
        dot_product_append(a.take(i + 1), b1, a[i + 1], val2);
        assert(a.take(i + 1).push(a[i + 1]) =~= a.take(i + 2));
        // dot_product(a.take(i+2), b2) == a[i]*a[i+1] + a[i+1]*(-a[i]) == 0
        // Help Verus with nonlinear arithmetic
        assert(a[i + 1] * (-a[i]) == -(a[i + 1] * a[i])) by(nonlinear_arith);
        assert(a[i] * a[i + 1] == a[i + 1] * a[i]) by(nonlinear_arith);
        assert(a[i] * a[i + 1] + a[i + 1] * (-a[i]) == 0) by(nonlinear_arith);
        push_preserves_non_zero(b1, val2);
        push_preserves_bounded(b1, val2, 100);
        let b2 = b1.push(val2);

        find_sasuke_rec(a, i + 2, b2)
    }
}

// Main proof entry point
proof fn find_sasuke(a: Seq<int>) -> (b: Seq<int>)
    requires
        a.len() % 2 == 0,
        all_non_zero(a),
        all_bounded(a, 100),
    ensures
        valid_solution(a, b),
{
    find_sasuke_rec(a, 0, Seq::empty())
}

fn main() {}

} // verus!

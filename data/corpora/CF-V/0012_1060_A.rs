use vstd::prelude::*;

verus! {

// Count occurrences of value v in sequence s
pub open spec fn count_occurrences(s: Seq<int>, v: int) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[s.len() - 1] == v { 1 as int } else { 0 as int })
            + count_occurrences(s.take(s.len() as int - 1), v)
    }
}

// Achievable predicate
pub open spec fn achievable(k: int, digits: Seq<int>) -> bool {
    k >= 0 && 11 * k <= digits.len() && k <= count_occurrences(digits, 8)
}

// Lemma: CountOccurrences is non-negative
pub proof fn count_occurrences_non_neg(s: Seq<int>, v: int)
    ensures
        count_occurrences(s, v) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        count_occurrences_non_neg(s.take(s.len() as int - 1), v);
    }
}

// Lemma: count_occurrences bounded by length
pub proof fn count_occurrences_bounded(s: Seq<int>, v: int)
    ensures
        count_occurrences(s, v) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        count_occurrences_bounded(s.take(s.len() as int - 1), v);
    }
}

// Helper lemma for the loop body
proof fn count_occurrences_snoc(s: Seq<int>, x: int, v: int)
    ensures
        count_occurrences(s.push(x), v) == count_occurrences(s, v) + (if x == v {
            1 as int
        } else {
            0 as int
        }),
{
    let s2 = s.push(x);
    assert(s2.len() == s.len() + 1);
    assert(s2[s2.len() - 1] == x);
    assert(s2.take(s2.len() as int - 1) =~= s);
}

// Main method
pub fn phone_numbers(n: i64, digits: &Vec<i64>) -> (count: i64)
    requires
        n == digits@.len(),
        n >= 0,
        n <= i64::MAX,
    ensures
        achievable(count as int, digits@.map(|_idx, x: i64| x as int)),
        !achievable(
            count as int + 1,
            digits@.map(|_idx, x: i64| x as int),
        ),
{
    let ghost digits_spec: Seq<int> = digits@.map(|_idx, x: i64| x as int);
    let mut cnt8: i64 = 0;
    for i in 0..digits.len()
        invariant
            0 <= cnt8 <= i as int,
            cnt8 == count_occurrences(digits_spec.take(i as int), 8),
            digits_spec =~= digits@.map(|_idx, x: i64| x as int),
            n == digits@.len(),
            i <= digits.len(),
            digits@.len() <= i64::MAX as int,
    {
        proof {
            let prefix = digits_spec.take(i as int);
            let elem = digits_spec[i as int];
            assert(digits_spec.take(i as int + 1) =~= prefix.push(elem));
            count_occurrences_snoc(prefix, elem, 8);
            count_occurrences_bounded(digits_spec.take(i as int), 8);
        }
        if digits[i] == 8 {
            cnt8 = cnt8 + 1;
        }
    }
    proof {
        assert(digits_spec.take(digits_spec.len() as int) =~= digits_spec);
        count_occurrences_non_neg(digits_spec, 8);
    }
    if cnt8 < n / 11 {
        cnt8
    } else {
        n / 11
    }
}

fn main() {}

} // verus!

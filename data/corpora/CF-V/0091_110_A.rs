use vstd::prelude::*;

verus! {

// --- Specification ---

pub open spec fn abs_val(n: int) -> nat {
    if n < 0 { (-n) as nat } else { n as nat }
}

pub open spec fn is_lucky_digit(d: int) -> bool {
    d == 4 || d == 7
}

// Decimal digits of a positive number (most-significant first); 0 maps to [].
pub open spec fn digits(n: nat) -> Seq<int>
    decreases n,
{
    if n == 0 {
        Seq::<int>::empty()
    } else {
        digits((n / 10) as nat).push((n % 10) as int)
    }
}

// Count of lucky digits in a sequence (slice-based recursion).
pub open spec fn count_lucky(s: Seq<int>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (count_lucky(s.take(s.len() - 1)) + if is_lucky_digit(s.last()) { 1nat } else { 0nat }) as nat
    }
}

// A lucky number is a positive integer whose every digit is 4 or 7.
pub open spec fn is_lucky_number(n: nat) -> bool {
    let d = digits(n);
    n > 0 && forall|i: int| 0 <= i < d.len() ==> is_lucky_digit(#[trigger] d[i])
}

// A number is nearly lucky iff the count of lucky digits in its
// decimal representation is itself a lucky number.
pub open spec fn is_nearly_lucky(n: int) -> bool {
    is_lucky_number(count_lucky(digits(abs_val(n))))
}

// --- Helper predicate and lemmas ---

// Bottom-up check: are all digits of n lucky?
pub open spec fn all_digits_lucky(n: nat) -> bool
    decreases n,
{
    if n == 0 {
        true
    } else {
        is_lucky_digit((n % 10) as int) && all_digits_lucky((n / 10) as nat)
    }
}

proof fn count_lucky_bound(s: Seq<int>)
    ensures
        count_lucky(s) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        count_lucky_bound(s.take(s.len() - 1));
    }
}

// Decompose CountLucky(Digits(n)) by peeling off the last digit.
pub proof fn count_lucky_decompose(n: nat)
    requires
        n > 0,
    ensures
        count_lucky(digits(n)) == count_lucky(digits((n / 10) as nat)) + (if is_lucky_digit((n % 10) as int) { 1nat } else { 0nat }),
{
    let d = digits(n);
    assert(d =~= digits((n / 10) as nat).push((n % 10) as int));
    assert(d.take(d.len() - 1) =~= digits((n / 10) as nat));
}

// AllDigitsLucky(n) <==> IsLuckyNumber(n) for n > 0.
pub proof fn all_digits_lucky_equiv(n: nat)
    requires
        n > 0,
    ensures
        all_digits_lucky(n) <==> is_lucky_number(n),
    decreases n,
{
    let d = digits(n);
    if n / 10 == 0 {
        assert(digits(0nat) =~= Seq::<int>::empty());
        assert(d =~= Seq::<int>::empty().push((n % 10) as int));
        assert(d.len() == 1);
        assert(d[0] == (n % 10) as int);
        assert(all_digits_lucky(n) == (is_lucky_digit((n % 10) as int) && all_digits_lucky(0nat)));
        assert(all_digits_lucky(0nat) == true);
        if is_lucky_digit((n % 10) as int) {
            assert(is_lucky_digit(d[0int]));
            assert forall|i: int| 0 <= i < d.len() implies is_lucky_digit(#[trigger] d[i]) by {
                assert(d.len() == 1);
            }
            assert(is_lucky_number(n));
        }
        if !is_lucky_digit((n % 10) as int) {
            assert(!all_digits_lucky(n));
            assert(!is_lucky_digit(d[0int]));
            assert(!is_lucky_number(n));
        }
    } else {
        all_digits_lucky_equiv((n / 10) as nat);
        let d2 = digits((n / 10) as nat);
        assert(d =~= d2.push((n % 10) as int));
        assert(d.len() == d2.len() + 1);

        if all_digits_lucky(n) {
            assert(is_lucky_digit((n % 10) as int));
            assert(all_digits_lucky((n / 10) as nat));
            assert(is_lucky_number((n / 10) as nat));
            assert forall|i: int| 0 <= i < d.len() implies is_lucky_digit(#[trigger] d[i]) by {
                if i < d2.len() {
                    assert(d[i] == d2[i]);
                    assert(is_lucky_digit(d2[i]));
                } else {
                    assert(i == d2.len());
                    assert(d[i] == (n % 10) as int);
                }
            }
            assert(is_lucky_number(n));
        }
        if is_lucky_number(n) {
            assert(d[d.len() - 1] == (n % 10) as int);
            assert(is_lucky_digit(d[(d.len() - 1) as int]));
            assert(is_lucky_digit((n % 10) as int));
            assert forall|i: int| 0 <= i < d2.len() implies is_lucky_digit(#[trigger] d2[i]) by {
                assert(d2[i] == d[i]);
            }
            assert(n / 10 > 0);
            assert(is_lucky_number((n / 10) as nat));
            assert(all_digits_lucky((n / 10) as nat));
            assert(all_digits_lucky(n));
        }
    }
}

// --- Implementation ---

// Number of decimal digits
spec fn num_digits(n: nat) -> nat
    decreases n,
{
    if n == 0 { 0nat } else { (1 + num_digits((n / 10) as nat)) as nat }
}

proof fn num_digits_bound(n: nat, k: nat)
    requires
        n < pow10(k),
    ensures
        num_digits(n) <= k,
    decreases n,
{
    if n > 0 {
        // k must be > 0 since n > 0 and n < pow10(k), and pow10(0) = 1
        assert(k > 0) by {
            if k == 0 {
                assert(pow10(0nat) == 1nat);
                assert(n < 1);  // contradiction with n > 0
            }
        }
        // n < 10^k => n/10 < 10^(k-1)
        assert(n / 10 < pow10((k - 1) as nat)) by(nonlinear_arith)
            requires n < pow10(k), k > 0, pow10(k) == 10 * pow10((k - 1) as nat);
        pow10_positive((k - 1) as nat);
        num_digits_bound((n / 10) as nat, (k - 1) as nat);
    }
}

spec fn pow10(k: nat) -> nat
    decreases k,
{
    if k == 0 { 1 } else { (10 * pow10((k - 1) as nat)) as nat }
}

proof fn pow10_positive(k: nat)
    ensures pow10(k) > 0,
    decreases k,
{
    if k > 0 {
        pow10_positive((k - 1) as nat);
    }
}

// count_lucky of digits of n is bounded by num_digits(n)
proof fn count_lucky_of_digits_bound(n: nat)
    ensures count_lucky(digits(n)) <= num_digits(n),
    decreases n,
{
    if n == 0 {
        assert(digits(0nat) =~= Seq::<int>::empty());
    } else {
        count_lucky_decompose(n);
        count_lucky_of_digits_bound((n / 10) as nat);
    }
}

pub fn nearly_lucky(n: i64) -> (result: bool)
    requires
        n > i64::MIN,
    ensures
        result == is_nearly_lucky(n as int),
{
    let num: i64 = if n < 0 { -n } else { n };
    assert(num as nat == abs_val(n as int));

    if num == 0 {
        return false;
    }

    proof {
        // num <= i64::MAX = 9223372036854775807 < 10^19
        // So num_digits(num) <= 19, and count_lucky(digits(num)) <= 19
        pow10_positive(19nat);
        assert(pow10(0nat) == 1nat);
        assert(pow10(1nat) == 10nat);
        assert(pow10(2nat) == 100nat);
        assert(pow10(3nat) == 1000nat);
        assert(pow10(4nat) == 10000nat);
        assert(pow10(5nat) == 100000nat);
        assert(pow10(6nat) == 1000000nat);
        assert(pow10(7nat) == 10000000nat);
        assert(pow10(8nat) == 100000000nat);
        assert(pow10(9nat) == 1000000000nat);
        assert(pow10(10nat) == 10000000000nat);
        assert(pow10(11nat) == 100000000000nat);
        assert(pow10(12nat) == 1000000000000nat);
        assert(pow10(13nat) == 10000000000000nat);
        assert(pow10(14nat) == 100000000000000nat);
        assert(pow10(15nat) == 1000000000000000nat);
        assert(pow10(16nat) == 10000000000000000nat);
        assert(pow10(17nat) == 100000000000000000nat);
        assert(pow10(18nat) == 1000000000000000000nat);
        assert(pow10(19nat) == 10000000000000000000nat);
        assert((num as nat) < pow10(19nat));
        num_digits_bound(num as nat, 19nat);
        count_lucky_of_digits_bound(num as nat);
    }

    let mut count: i64 = 0;
    let mut temp: i64 = num;

    while temp > 0
        invariant
            temp >= 0,
            count >= 0,
            num > 0,
            count as nat + count_lucky(digits(temp as nat)) == count_lucky(digits(num as nat)),
            count_lucky(digits(num as nat)) <= 19,
        decreases temp,
    {
        proof {
            count_lucky_decompose(temp as nat);
        }
        let digit = temp % 10;
        if digit == 4 || digit == 7 {
            count = count + 1;
        }
        temp = temp / 10;
    }

    assert(count as nat == count_lucky(digits(abs_val(n as int))));

    if count == 0 {
        return false;
    }

    let mut flag: bool = true;
    temp = count;

    while temp > 0
        invariant
            temp >= 0,
            count > 0,
            count <= 19,
            (flag && all_digits_lucky(temp as nat)) <==> all_digits_lucky(count as nat),
        decreases temp,
    {
        let digit = temp % 10;
        if digit != 4 && digit != 7 {
            flag = false;
        }
        temp = temp / 10;
    }

    proof {
        all_digits_lucky_equiv(count as nat);
    }
    flag
}

fn main() {}

} // verus!

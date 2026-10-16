use vstd::prelude::*;

verus! {

// ghost predicate IsDigitChar
spec fn is_digit_char(c: char) -> bool {
    '0' <= c && c <= '9'
}

// ghost predicate AllDigits
spec fn all_digits(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> is_digit_char(#[trigger] s[i])
}

// ghost function DigitVal
spec fn digit_val(c: char) -> int
    recommends is_digit_char(c)
{
    (c as int) - ('0' as int)
}

// ghost function StringToNat
spec fn string_to_nat(s: Seq<char>) -> int
    recommends s.len() > 0, all_digits(s)
    decreases s.len()
{
    if s.len() == 1 {
        digit_val(s[0])
    } else if s.len() > 1 {
        string_to_nat(s.subrange(0, s.len() - 1)) * 10 + digit_val(s[s.len() - 1])
    } else {
        0 // unreachable
    }
}

// ghost function CountEvenEndingHere
spec fn count_even_ending_here(s: Seq<char>) -> int
    recommends s.len() > 0, all_digits(s)
    decreases s.len()
{
    let this_one: int = if string_to_nat(s) % 2 == 0 { 1 } else { 0 };
    if s.len() == 1 {
        this_one
    } else if s.len() > 1 {
        this_one + count_even_ending_here(s.subrange(1, s.len() as int))
    } else {
        0 // unreachable
    }
}

// ghost function CountEvenSubstrings
spec fn count_even_substrings(s: Seq<char>) -> int
    recommends all_digits(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_even_substrings(s.subrange(0, s.len() - 1)) + count_even_ending_here(s)
    }
}

// lemma ParityLemma
proof fn parity_lemma(s: Seq<char>)
    requires
        s.len() > 0,
        all_digits(s),
    ensures
        string_to_nat(s) % 2 == digit_val(s[s.len() - 1]) % 2,
    decreases s.len()
{
    if s.len() == 1 {
    } else {
        assert(string_to_nat(s) == string_to_nat(s.subrange(0, s.len() - 1)) * 10 + digit_val(s[s.len() - 1]));
        let k = string_to_nat(s.subrange(0, s.len() - 1));
        let d = digit_val(s[s.len() - 1]);
        assert((k * 10 + d) % 2 == d % 2) by(nonlinear_arith)
            requires
                string_to_nat(s) == k * 10 + d,
        {}
    }
}

// lemma CountEvenEndingHereValue
proof fn count_even_ending_here_value(s: Seq<char>)
    requires
        s.len() > 0,
        all_digits(s),
    ensures
        digit_val(s[s.len() - 1]) % 2 == 0 ==> count_even_ending_here(s) == s.len(),
        digit_val(s[s.len() - 1]) % 2 != 0 ==> count_even_ending_here(s) == 0,
    decreases s.len()
{
    parity_lemma(s);
    if s.len() == 1 {
    } else {
        let tail = s.subrange(1, s.len() as int);
        assert(tail[tail.len() - 1] == s[s.len() - 1]);
        assert(all_digits(tail)) by {
            assert forall|i: int| 0 <= i < tail.len() implies is_digit_char(#[trigger] tail[i]) by {
                assert(tail[i] == s[i + 1]);
            }
        }
        count_even_ending_here_value(tail);
    }
}

// Bound lemma: count_even_ending_here is between 0 and |s|
proof fn count_even_ending_here_bound(s: Seq<char>)
    requires
        s.len() > 0,
        all_digits(s),
    ensures
        0 <= count_even_ending_here(s) <= s.len(),
    decreases s.len()
{
    count_even_ending_here_value(s);
}

// Bound lemma: count_even_substrings is between 0 and n*(n+1)/2
proof fn count_even_substrings_bound(s: Seq<char>)
    requires
        all_digits(s),
    ensures
        0 <= count_even_substrings(s),
        count_even_substrings(s) <= s.len() * (s.len() + 1) / 2,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let prefix = s.subrange(0, s.len() - 1);
        assert(all_digits(prefix)) by {
            assert forall|i: int| 0 <= i < prefix.len() implies is_digit_char(#[trigger] prefix[i]) by {
                assert(prefix[i] == s[i]);
            }
        }
        count_even_substrings_bound(prefix);
        count_even_ending_here_bound(s);
        // prefix.len() == s.len() - 1
        // count_even_substrings(prefix) <= (s.len()-1)*s.len()/2
        // count_even_ending_here(s) <= s.len()
        // sum <= (s.len()-1)*s.len()/2 + s.len() = s.len()*((s.len()-1)/2 + 1) = s.len()*(s.len()+1)/2
        assert(count_even_substrings(s) <= s.len() * (s.len() + 1) / 2) by(nonlinear_arith)
            requires
                count_even_substrings(prefix) <= prefix.len() * (prefix.len() + 1) / 2,
                count_even_ending_here(s) <= s.len(),
                count_even_substrings(s) == count_even_substrings(prefix) + count_even_ending_here(s),
                prefix.len() == s.len() - 1,
                count_even_substrings(prefix) >= 0,
                count_even_ending_here(s) >= 0,
        {}
    }
}

// method EvenSubstrings
fn even_substrings(s: &Vec<char>) -> (count: i64)
    requires
        all_digits(s@),
        s@.len() < 100_000,
    ensures
        count == count_even_substrings(s@),
{
    let mut count: i64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            s@.len() < 100_000,
            all_digits(s@),
            count == count_even_substrings(s@.subrange(0, i as int)),
            count >= 0,
            count <= i * (i + 1) / 2,
        decreases s.len() - i,
    {
        // assert s[..i+1][..i] == s[..i]
        proof {
            assert(s@.subrange(0, (i + 1) as int).subrange(0, i as int) =~= s@.subrange(0, i as int));
        }

        // CountEvenEndingHereValue(s[..i+1])
        proof {
            let p = s@.subrange(0, (i + 1) as int);
            assert(all_digits(p)) by {
                assert forall|j: int| 0 <= j < p.len() implies is_digit_char(#[trigger] p[j]) by {
                    assert(p[j] == s@[j]);
                }
            }
            count_even_ending_here_value(p);
        }

        // assert s[..i+1][|s[..i+1]|-1] == s[i]
        proof {
            let p = s@.subrange(0, (i + 1) as int);
            assert(p[p.len() - 1] == s@[i as int]);
        }

        let c = s[i];
        if c == '0' || c == '2' || c == '4' || c == '6' || c == '8' {
            // count_even_ending_here(s[..i+1]) == i+1 (even last digit)
            // new count = old count + i + 1
            // old count <= i*(i+1)/2, new count <= i*(i+1)/2 + i + 1 = (i+1)*(i+2)/2
            assert(count + (i as i64) + 1 <= (i + 1) * (i + 2) / 2) by(nonlinear_arith)
                requires
                    count <= i * (i + 1) / 2,
                    count >= 0,
                    i < 100_000,
            {}
            assert((i + 1) * (i + 2) / 2 < 5_000_100_000i64) by(nonlinear_arith)
                requires i < 100_000,
            {}
            assert(count + (i as i64) + 1 < 5_000_100_000i64);
            count = count + (i as i64) + 1;
        } else {
            // count_even_ending_here(s[..i+1]) == 0 (odd last digit)
            // new count = old count
            assert(count <= (i + 1) * (i + 2) / 2) by(nonlinear_arith)
                requires
                    count <= i * (i + 1) / 2,
                    count >= 0,
                    i < 100_000,
            {}
        }
        i = i + 1;
    }
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }
    count
}

fn main() {}

} // verus!

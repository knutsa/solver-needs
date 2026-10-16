use vstd::prelude::*;

verus! {

// A good string consists of only 'a' and 'b' with every two consecutive letters distinct.
spec fn is_good_string(s: Seq<char>) -> bool {
    (forall|i: int| 0 <= i < s.len() ==> (#[trigger] s[i] == 'a' || s[i] == 'b'))
    && (forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] != #[trigger] s[i + 1])
}

// A good string with na 'a'-characters and nb 'b'-characters exists iff
// both counts are non-negative and they differ by at most 1.
spec fn good_string_with_counts(na: int, nb: int) -> bool {
    na >= 0 && nb >= 0 && na - nb <= 1 && nb - na <= 1
}

// Helper to avoid trigger issues with nested exists
spec fn valid_selection(pa: int, pb: int, pc: int, len: int, a: int, b: int, c: int) -> bool {
    0 <= pa <= a && 0 <= pb <= b && 0 <= pc <= c
    && good_string_with_counts(pa + pc, pb + pc)
    && pa + pb + 2 * pc == len
}

// Whether a good string of exactly `len` characters can be formed
spec fn achievable_length(len: int, a: int, b: int, c: int) -> bool {
    a >= 0 && b >= 0 && c >= 0
    && exists|pa: int, pb: int, pc: int| #[trigger] valid_selection(pa, pb, pc, len, a, b, c)
}

proof fn achievable_witness(len: int, a: int, b: int, c: int, pa: int, pb: int, pc: int)
    requires
        a >= 0 && b >= 0 && c >= 0,
        0 <= pa <= a && 0 <= pb <= b && 0 <= pc <= c,
        good_string_with_counts(pa + pc, pb + pc),
        pa + pb + 2 * pc == len,
    ensures
        achievable_length(len, a, b, c),
{
    assert(valid_selection(pa, pb, pc, len, a, b, c));
}

proof fn not_achievable(n: int, a: int, b: int, c: int, max_len: int)
    requires
        a >= 0 && b >= 0 && c >= 0,
        n > max_len,
        if a == b { max_len == 2 * a + 2 * c }
        else if a > b { max_len == 2 * b + 2 * c + 1 }
        else { max_len == 2 * a + 2 * c + 1 },
    ensures
        !achievable_length(n, a, b, c),
{
    if achievable_length(n, a, b, c) {
        let (pa, pb, pc) = choose|pa: int, pb: int, pc: int| #[trigger] valid_selection(pa, pb, pc, n, a, b, c);
        assert(valid_selection(pa, pb, pc, n, a, b, c));
        // Extract facts from valid_selection and good_string_with_counts
        assert(0 <= pa && pa <= a);
        assert(0 <= pb && pb <= b);
        assert(0 <= pc && pc <= c);
        assert(pa + pc >= 0);
        assert(pb + pc >= 0);
        assert((pa + pc) - (pb + pc) <= 1);
        assert((pb + pc) - (pa + pc) <= 1);
        assert(pa + pb + 2 * pc == n);
        // (pa + pc) - (pb + pc) = pa - pb <= 1 and pb - pa <= 1
        // In all cases, we derive n <= max_len, contradiction with n > max_len
        if a == b {
            // pa <= a, pb <= a, pa - pb <= 1 and pb - pa <= 1
            // pa + pb <= a + a = 2a
            // n = pa + pb + 2*pc <= 2a + 2c = max_len
            assert(n <= max_len);
        } else if a > b {
            // pa - pb <= 1, pb <= b => pa <= b + 1
            // n = pa + pb + 2pc <= (b+1) + b + 2c = 2b + 1 + 2c = max_len
            assert(pa <= b + 1);
            assert(n <= max_len);
        } else {
            // pb - pa <= 1, pa <= a => pb <= a + 1
            // n = pa + pb + 2pc <= a + (a+1) + 2c = 2a + 1 + 2c = max_len
            assert(pb <= a + 1);
            assert(n <= max_len);
        }
    }
}

fn another_one_bites_the_dust(a: i64, b: i64, c: i64) -> (max_len: i64)
    requires
        a >= 0 && b >= 0 && c >= 0,
        a + b + 2 * c <= i64::MAX,
    ensures
        achievable_length(max_len as int, a as int, b as int, c as int),
        forall|n: int| max_len < n <= a + b + 2 * c ==> !achievable_length(n, a as int, b as int, c as int),
{
    let mut x: i64 = a + c;
    let mut y: i64 = b + c;

    if x > y {
        x = y + 1;
    }
    if y > x {
        y = x + 1;
    }

    let max_len: i64 = x + y;

    proof {
        if a > b {
            achievable_witness(max_len as int, a as int, b as int, c as int, (b + 1) as int, b as int, c as int);
        } else if a < b {
            achievable_witness(max_len as int, a as int, b as int, c as int, a as int, (a + 1) as int, c as int);
        } else {
            achievable_witness(max_len as int, a as int, b as int, c as int, a as int, b as int, c as int);
        }

        assert(
            if a == b { max_len == 2 * a + 2 * c }
            else if a > b { max_len == 2 * b + 2 * c + 1 }
            else { max_len == 2 * a + 2 * c + 1 }
        );

        assert forall|n: int| max_len < n <= a + b + 2 * c implies !achievable_length(n, a as int, b as int, c as int) by {
            not_achievable(n, a as int, b as int, c as int, max_len as int);
        }
    }

    max_len
}

fn main() {}

} // verus!

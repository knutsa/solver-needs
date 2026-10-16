use vstd::prelude::*;

verus! {

// A digit is a character code in ['0', '9'] = [48, 57]
pub open spec fn is_digit(c: u8) -> bool {
    48 <= c && c <= 57
}

// CanFormPhone(s, remaining): can we pick `remaining` digits from s (in order)
// such that the first picked digit is '8' (= 56) and all are digits?
pub open spec fn can_form_phone(s: Seq<u8>, remaining: nat) -> bool
    decreases s.len(),
{
    if remaining == 0 {
        true
    } else if s.len() == 0 {
        false
    } else {
        // Skip s[0]
        can_form_phone(s.subrange(1, s.len() as int), remaining)
        ||
        // Select s[0] as the next phone-number digit
        (is_digit(s[0]) && (remaining == 11 ==> s[0] == 56) && can_form_phone(s.subrange(1, s.len() as int), (remaining - 1) as nat))
    }
}

// When we have enough digits and remaining <= 10, we can always form the phone suffix.
proof fn can_form_phone_all_digits(t: Seq<u8>, r: nat)
    requires
        r <= 10,
        t.len() >= r,
        forall|i: int| 0 <= i < t.len() ==> is_digit(#[trigger] t[i]),
    ensures
        can_form_phone(t, r),
    decreases t.len(),
{
    if r == 0 {
    } else {
        let tail = t.subrange(1, t.len() as int);
        assert forall|i: int| 0 <= i < tail.len() implies is_digit(#[trigger] tail[i]) by {
            assert(tail[i] == t[i + 1]);
        }
        can_form_phone_all_digits(tail, (r - 1) as nat);
    }
}

// If the first character is not '8', it cannot start a phone number,
// so can_form_phone(t, 11) reduces to skipping it.
proof fn can_form_phone_skip_non8(t: Seq<u8>)
    requires
        t.len() >= 11,
        forall|i: int| 0 <= i < t.len() ==> is_digit(#[trigger] t[i]),
        t[0] != 56,
    ensures
        can_form_phone(t, 11nat) == can_form_phone(t.subrange(1, t.len() as int), 11nat),
{
    // The "select s[0]" branch requires s[0] == '8' when remaining == 11,
    // which fails since t[0] != '8'. So only the skip branch matters.
}

// If the first character is '8' and we have >= 11 characters (all digits),
// we can form a phone number.
proof fn can_form_phone_found8(t: Seq<u8>)
    requires
        t.len() >= 11,
        forall|i: int| 0 <= i < t.len() ==> is_digit(#[trigger] t[i]),
        t[0] == 56,
    ensures
        can_form_phone(t, 11nat),
{
    let tail = t.subrange(1, t.len() as int);
    assert forall|i: int| 0 <= i < tail.len() implies is_digit(#[trigger] tail[i]) by {
        assert(tail[i] == t[i + 1]);
    }
    can_form_phone_all_digits(tail, 10nat);
}

// If the sequence is shorter than remaining, we cannot form a phone number.
proof fn can_form_phone_too_short(t: Seq<u8>, r: nat)
    requires
        t.len() < r,
        r > 0,
    ensures
        !can_form_phone(t, r),
    decreases t.len(),
{
    if t.len() == 0 {
    } else {
        let tail = t.subrange(1, t.len() as int);
        can_form_phone_too_short(tail, r);
        if r > 1 {
            can_form_phone_too_short(tail, (r - 1) as nat);
        }
    }
}

// Helper: subrange(i+1, len) of subrange(i, len) equals subrange(i+1, len)
proof fn subrange_shift(s: Seq<u8>, i: int)
    requires
        0 <= i,
        i + 1 <= s.len(),
    ensures
        s.subrange(i, s.len() as int).subrange(1, s.subrange(i, s.len() as int).len() as int)
            =~= s.subrange(i + 1, s.len() as int),
{
}

fn telephone_number(s: &Vec<u8>, n: usize) -> (result: bool)
    requires
        n == s@.len(),
        forall|i: int| 0 <= i < n as int ==> is_digit(#[trigger] s@[i]),
    ensures
        result == can_form_phone(s@, 11nat),
{
    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }

    let mut i: usize = 0;

    while i < n && n - i > 10
        invariant
            0 <= i <= n,
            n == s@.len(),
            forall|j: int| 0 <= j < n as int ==> is_digit(#[trigger] s@[j]),
            can_form_phone(s@, 11nat) == can_form_phone(s@.subrange(i as int, s@.len() as int), 11nat),
        decreases n - i,
    {
        proof {
            let si = s@.subrange(i as int, s@.len() as int);
            assert(si.len() >= 11);
            assert(si[0] == s@[i as int]);
            assert forall|j: int| 0 <= j < si.len() implies is_digit(#[trigger] si[j]) by {
                assert(si[j] == s@[j + i as int]);
            }
        }

        if s[i] == 56 {  // '8'
            proof {
                let si = s@.subrange(i as int, s@.len() as int);
                can_form_phone_found8(si);
            }
            return true;
        }

        proof {
            let si = s@.subrange(i as int, s@.len() as int);
            can_form_phone_skip_non8(si);
            subrange_shift(s@, i as int);
        }

        i = i + 1;
    }

    proof {
        let tail = s@.subrange(i as int, s@.len() as int);
        assert(tail.len() < 11);
        can_form_phone_too_short(tail, 11nat);
    }

    return false;
}

fn main() {}

} // verus!

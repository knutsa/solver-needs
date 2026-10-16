use vstd::prelude::*;

verus! {

spec fn valid_ab(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == 'a' || s[i] == 'b'
}

spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_char(s.subrange(0, s.len() - 1), c)
            + if s[s.len() - 1] == c { 1 as int } else { 0 as int }
    }
}

spec fn balanced_prefixes(s: Seq<char>) -> bool {
    forall|k: int|
        1 <= k <= s.len() / 2 ==> #[trigger] count_char(s.subrange(0, 2 * k), 'a') == count_char(
            s.subrange(0, 2 * k),
            'b',
        )
}

spec fn hamming_dist(s: Seq<char>, t: Seq<char>) -> int
    recommends s.len() == t.len(),
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        hamming_dist(s.subrange(0, s.len() - 1), t.subrange(0, t.len() - 1))
            + if s[s.len() - 1] != t[s.len() - 1] { 1 as int } else { 0 as int }
    }
}

spec fn count_bad_pairs(s: Seq<char>) -> int
    recommends s.len() % 2 == 0,
    decreases s.len(),
{
    if s.len() < 2 {
        0
    } else {
        count_bad_pairs(s.subrange(0, s.len() - 2))
            + if s[s.len() - 2] == s[s.len() - 1] { 1 as int } else { 0 as int }
    }
}

proof fn count_char_append(s: Seq<char>, c: char, ch: char)
    ensures
        count_char(s.push(c), ch) == count_char(s, ch) + (if c == ch { 1 as int } else {
            0 as int
        }),
{
    assert(s.push(c).subrange(0, s.len() as int) =~= s);
}

proof fn count_char_append2(s: Seq<char>, a: char, b: char, ch: char)
    ensures
        count_char(s + seq![a, b], ch) == count_char(s, ch) + (if a == ch {
            1 as int
        } else {
            0 as int
        }) + (if b == ch { 1 as int } else { 0 as int }),
{
    assert(s + seq![a, b] =~= s.push(a).push(b));
    let sa = s.push(a);
    count_char_append(sa, b, ch);
    count_char_append(s, a, ch);
}

proof fn hamming_dist_append(s1: Seq<char>, s2: Seq<char>, a: char, b: char)
    requires
        s1.len() == s2.len(),
    ensures
        hamming_dist(s1.push(a), s2.push(b)) == hamming_dist(s1, s2) + (if a != b {
            1 as int
        } else {
            0 as int
        }),
{
    assert(s1.push(a).subrange(0, s1.len() as int) =~= s1);
    assert(s2.push(b).subrange(0, s2.len() as int) =~= s2);
}

proof fn hamming_dist_append2(
    s1: Seq<char>,
    s2: Seq<char>,
    a1: char,
    a2: char,
    b1: char,
    b2: char,
)
    requires
        s1.len() == s2.len(),
    ensures
        hamming_dist(s1 + seq![a1, a2], s2 + seq![b1, b2]) == hamming_dist(s1, s2) + (if a1
            != b1 {
            1 as int
        } else {
            0 as int
        }) + (if a2 != b2 { 1 as int } else { 0 as int }),
{
    assert(s1 + seq![a1, a2] =~= s1.push(a1).push(a2));
    assert(s2 + seq![b1, b2] =~= s2.push(b1).push(b2));
    hamming_dist_append(s1.push(a1), s2.push(b1), a2, b2);
    hamming_dist_append(s1, s2, a1, b1);
}

proof fn count_bad_pairs_step(s: Seq<char>, a: char, b: char)
    requires
        s.len() % 2 == 0,
    ensures
        (s + seq![a, b]).len() % 2 == 0,
        count_bad_pairs(s + seq![a, b]) == count_bad_pairs(s) + (if a == b {
            1 as int
        } else {
            0 as int
        }),
{
    let s2 = s + seq![a, b];
    assert(s2 =~= s.push(a).push(b));
    assert(s2.subrange(0, s2.len() - 2) =~= s);
}

proof fn balanced_prefixes_extend(result: Seq<char>, a: char, b: char)
    requires
        result.len() % 2 == 0,
        balanced_prefixes(result),
        count_char(result, 'a') == count_char(result, 'b'),
        (a == 'a' && b == 'b') || (a == 'b' && b == 'a'),
    ensures
        balanced_prefixes(result + seq![a, b]),
{
    let r = result + seq![a, b];
    assert(r =~= result.push(a).push(b));
    count_char_append2(result, a, b, 'a');
    count_char_append2(result, a, b, 'b');
    assert forall|k: int|
        1 <= k <= r.len() / 2 implies #[trigger] count_char(r.subrange(0, 2 * k), 'a')
        == count_char(r.subrange(0, 2 * k), 'b') by {
        if 2 * k <= result.len() {
            assert(r.subrange(0, 2 * k) =~= result.subrange(0, 2 * k));
        } else {
            assert(2 * k == r.len());
            assert(r.subrange(0, 2 * k) =~= r);
        }
    }
}

proof fn count_bad_pairs_bound(s: Seq<char>)
    requires
        s.len() % 2 == 0,
    ensures
        0 <= count_bad_pairs(s) <= s.len() / 2,
    decreases s.len(),
{
    if s.len() >= 2 {
        assert(s.subrange(0, s.len() - 2).len() == s.len() - 2);
        count_bad_pairs_bound(s.subrange(0, s.len() - 2));
    }
}

fn prefixes(s: &Vec<char>) -> (ret: (i64, Vec<char>))
    requires
        s@.len() % 2 == 0,
        valid_ab(s@),
        s@.len() < 0x7FFF_FFFF_FFFF_FFFE,
    ensures
        ({
            let (ops, result) = ret;
            result@.len() == s@.len() && valid_ab(result@) && balanced_prefixes(result@)
                && ops == hamming_dist(s@, result@) && ops == count_bad_pairs(s@)
        }),
{
    let mut ops: i64 = 0;
    let mut result: Vec<char> = Vec::new();
    let mut i: usize = 0;

    proof {
        count_bad_pairs_bound(s@.subrange(0, 0));
    }

    while i < s.len()
        invariant
            0 <= i <= s@.len(),
            i % 2 == 0,
            result@.len() == i as int,
            valid_ab(result@),
            ops == count_bad_pairs(s@.subrange(0, i as int)),
            count_char(result@, 'a') == (i as int) / 2,
            count_char(result@, 'b') == (i as int) / 2,
            balanced_prefixes(result@),
            ops == hamming_dist(s@.subrange(0, i as int), result@),
            s@.len() < 0x7FFF_FFFF_FFFF_FFFE,
            s@.len() % 2 == 0,
            valid_ab(s@),
            0 <= ops <= (i as int) / 2,
        decreases s@.len() - i,
    {
        proof {
            // i % 2 == 0, s@.len() % 2 == 0, i < s@.len() implies i + 1 < s@.len()
            assert(i + 1 < s@.len()) by {
                assert(s@.len() % 2 == 0);
                assert(i % 2 == 0);
                // i < s@.len() and both even means i + 1 < s@.len()
            };
        }
        let a: char;
        let b: char;
        if s[i] == s[i + 1] {
            a = 'a';
            b = 'b';
            ops = ops + 1;
        } else {
            a = s[i];
            b = s[i + 1];
        }

        proof {
            assert(s@.subrange(0, i as int) + seq![s@[i as int], s@[(i + 1) as int]]
                =~= s@.subrange(0, (i + 2) as int));
            count_bad_pairs_step(
                s@.subrange(0, i as int),
                s@[i as int],
                s@[(i + 1) as int],
            );
            hamming_dist_append2(
                s@.subrange(0, i as int),
                result@,
                s@[i as int],
                s@[(i + 1) as int],
                a,
                b,
            );
            count_char_append2(result@, a, b, 'a');
            count_char_append2(result@, a, b, 'b');
            balanced_prefixes_extend(result@, a, b);
            assert(result@ + seq![a, b] =~= result@.push(a).push(b));
            count_bad_pairs_bound(s@.subrange(0, (i + 2) as int));
        }

        result.push(a);
        result.push(b);
        i = i + 2;
    }

    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }

    (ops, result)
}

fn main() {}

} // verus!

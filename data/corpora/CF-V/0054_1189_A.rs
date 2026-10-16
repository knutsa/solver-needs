use vstd::prelude::*;

verus! {

// Ghost function: count occurrences of character c in sequence s
pub open spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        count_char(s.subrange(0, s.len() - 1), c)
            + if s[s.len() - 1] == c { 1 as int } else { 0 as int }
    }
}

// Ghost predicate: a string is "good" if count of '0' != count of '1'
pub open spec fn is_good(s: Seq<char>) -> bool {
    count_char(s, '0') != count_char(s, '1')
}

// Ghost predicate: string contains only '0' and '1'
pub open spec fn is_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

// Ghost function: flatten a sequence of strings into one string
pub open spec fn flatten(parts: Seq<Seq<char>>) -> Seq<char>
    decreases parts.len(),
{
    if parts.len() == 0 {
        Seq::<char>::empty()
    } else {
        flatten(parts.subrange(0, parts.len() - 1)) + parts[parts.len() - 1]
    }
}

// Ghost predicate: all parts are good
pub open spec fn all_good(parts: Seq<Seq<char>>) -> bool {
    forall|i: int| 0 <= i < parts.len() ==> is_good(parts[i])
}

// Lemma: for binary strings, count('0') + count('1') == length
proof fn count_char_sum(s: Seq<char>)
    requires
        is_binary_string(s),
    ensures
        count_char(s, '0') + count_char(s, '1') == s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        let prefix = s.subrange(0, s.len() - 1);
        assert forall|i: int| 0 <= i < prefix.len() implies (prefix[i] == '0' || prefix[i] == '1') by {
            assert(prefix[i] == s[i]);
        }
        count_char_sum(prefix);
    }
}

// Lemma: flatten of singleton is the element itself
proof fn flatten_singleton(x: Seq<char>)
    ensures
        flatten(seq![x]) =~= x,
{
    assert(seq![x].subrange(0, 0) =~= Seq::<Seq<char>>::empty());
    assert(seq![x][0] =~= x);
    assert(flatten(Seq::<Seq<char>>::empty()) =~= Seq::<char>::empty());
}

// Lemma: flatten of pair is concatenation
proof fn flatten_pair(a: Seq<char>, b: Seq<char>)
    ensures
        flatten(seq![a, b]) =~= a + b,
{
    assert(seq![a, b].subrange(0, 1) =~= seq![a]);
    assert(seq![a, b][1] =~= b);
    flatten_singleton(a);
}

// Main method
fn keanu_reeves(s: &Vec<char>) -> (result: (usize, Vec<Vec<char>>))
    requires
        s.len() > 0,
        is_binary_string(s@),
    ensures
        ({
            let (k, parts) = result;
            &&& k == parts.len()
            &&& (k == 1 || k == 2)
            &&& flatten(parts@.map_values(|v: Vec<char>| v@)) =~= s@
            &&& all_good(parts@.map_values(|v: Vec<char>| v@))
            &&& (k == 1 <==> is_good(s@))
        }),
{
    let mut zeros: usize = 0;
    let mut ones: usize = 0;
    let mut i: usize = 0;

    while i < s.len()
        invariant
            0 <= i <= s.len(),
            zeros == count_char(s@.subrange(0, i as int), '0'),
            ones == count_char(s@.subrange(0, i as int), '1'),
            // bounds to prevent overflow
            zeros <= i,
            ones <= i,
            is_binary_string(s@),
        decreases s.len() - i,
    {
        proof {
            let old_prefix = s@.subrange(0, i as int);
            let new_prefix = s@.subrange(0, (i + 1) as int);
            assert(new_prefix.subrange(0, new_prefix.len() - 1) =~= old_prefix);
        }
        if s[i] == '0' {
            zeros = zeros + 1;
        } else {
            ones = ones + 1;
        }
        i = i + 1;
    }

    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }

    if zeros != ones {
        let parts: Vec<Vec<char>> = vec![s.clone()];
        proof {
            flatten_singleton(s@);
            let spec_parts: Seq<Seq<char>> = parts@.map_values(|v: Vec<char>| v@);
            assert(spec_parts =~= seq![s@]);
            assert(is_good(s@));
            assert(all_good(spec_parts)) by {
                assert forall|i: int| 0 <= i < spec_parts.len() implies is_good(spec_parts[i]) by {
                    assert(spec_parts[0] =~= s@);
                }
            }
        }
        (1, parts)
    } else {
        let slen = s.len();
        let mut first: Vec<char> = Vec::new();
        let mut j: usize = 0;
        while j < slen - 1
            invariant
                0 <= j <= slen - 1,
                slen == s.len(),
                first.len() == j,
                forall|k: int| 0 <= k < j as int ==> first@[k] == s@[k],
            decreases slen - 1 - j,
        {
            first.push(s[j]);
            j = j + 1;
        }
        let second: Vec<char> = vec![s[slen - 1]];
        let parts: Vec<Vec<char>> = vec![first.clone(), second.clone()];

        proof {
            // first@ =~= s@.subrange(0, s@.len() - 1)
            assert(first@ =~= s@.subrange(0, s@.len() - 1));
            // second@ =~= seq![s@[s@.len() - 1]]
            assert(second@ =~= seq![s@[s@.len() - 1]]);
            // first + second == s
            assert(first@ + second@ =~= s@);

            flatten_pair(first@, second@);

            let spec_parts: Seq<Seq<char>> = parts@.map_values(|v: Vec<char>| v@);
            assert(spec_parts =~= seq![first@, second@]);

            // first is good
            let first_spec = first@;
            assert(is_binary_string(first_spec)) by {
                assert forall|i: int| 0 <= i < first_spec.len() implies (first_spec[i] == '0' || first_spec[i] == '1') by {
                    assert(first_spec[i] == s@[i]);
                }
            }
            count_char_sum(s@);
            count_char_sum(first_spec);
            // zeros == ones means count('0',s) == count('1',s) == |s|/2
            // first has length |s|-1, which is odd length difference
            // count_char(first,'0') + count_char(first,'1') == |s|-1
            // count_char(s,'0') + count_char(s,'1') == |s|
            // Since count_char(s,'0') == count_char(s,'1'), |s| is even
            // first has odd length, so count_char(first,'0') != count_char(first,'1')
            assert(count_char(s@, '0') == count_char(s@, '1'));
            // count_char(s, c) = count_char(first, c) + (if last==c then 1 else 0)
            assert(s@.subrange(0, s@.len() - 1) =~= first_spec);
            assert(is_good(first_spec));

            // second is good: single character
            let second_spec = second@;
            assert(is_good(second_spec)) by {
                assert(second_spec.len() == 1);
                assert(second_spec.subrange(0, 0) =~= Seq::<char>::empty());
                assert(count_char(Seq::<char>::empty(), '0') == 0);
                assert(count_char(Seq::<char>::empty(), '1') == 0);
                // count_char(second, '0') is 0 or 1, count_char(second, '1') is 0 or 1
                // and they can't both be 1 since there's only one char
            }

            // all_good
            assert(all_good(spec_parts)) by {
                assert forall|i: int| 0 <= i < spec_parts.len() implies is_good(spec_parts[i]) by {
                    if i == 0 {
                        assert(spec_parts[0] =~= first@);
                    } else {
                        assert(spec_parts[1] =~= second@);
                    }
                }
            }
        }
        (2, parts)
    }
}

fn main() {}

} // verus!

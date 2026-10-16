use vstd::prelude::*;

verus! {

// Build suffix sequences concretely so Verus knows their length and elements
spec fn po_seq() -> Seq<char> { seq!['p', 'o'] }
spec fn desu_seq() -> Seq<char> { seq!['d', 'e', 's', 'u'] }
spec fn masu_seq() -> Seq<char> { seq!['m', 'a', 's', 'u'] }
spec fn mnida_seq() -> Seq<char> { seq!['m', 'n', 'i', 'd', 'a'] }

spec fn ends_with(s: Seq<char>, suffix: Seq<char>) -> bool {
    s.len() >= suffix.len() &&
    forall|k: int| 0 <= k < suffix.len() ==>
        s.index(s.len() - suffix.len() + k) == #[trigger] suffix.index(k)
}

spec fn valid_sentence(s: Seq<char>) -> bool {
    ends_with(s, po_seq()) || ends_with(s, desu_seq()) || ends_with(s, masu_seq()) || ends_with(s, mnida_seq())
}

spec fn classify_sentence(s: Seq<char>) -> Seq<char>
{
    if ends_with(s, po_seq()) {
        "FILIPINO"@
    } else if ends_with(s, desu_seq()) || ends_with(s, masu_seq()) {
        "JAPANESE"@
    } else {
        "KOREAN"@
    }
}

spec fn classify_all(sentences: Seq<Seq<char>>) -> Seq<Seq<char>>
    decreases sentences.len()
{
    if sentences.len() == 0 {
        seq![]
    } else {
        classify_all(sentences.take(sentences.len() as int - 1)).push(
            classify_sentence(sentences.index(sentences.len() as int - 1))
        )
    }
}

proof fn classify_all_append(sentences: Seq<Seq<char>>)
    requires
        sentences.len() > 0,
        forall|i: int| 0 <= i < sentences.len() ==> valid_sentence(#[trigger] sentences.index(i)),
    ensures
        classify_all(sentences) =~= classify_all(sentences.take(sentences.len() as int - 1)).push(
            classify_sentence(sentences.index(sentences.len() as int - 1))
        ),
{
}

proof fn ends_with_last_char(s: Seq<char>, suffix: Seq<char>)
    requires
        ends_with(s, suffix),
        suffix.len() > 0,
    ensures
        s.index(s.len() as int - 1) == suffix.index(suffix.len() as int - 1),
{
    // Instantiate the forall with k = suffix.len() - 1
    let k = suffix.len() as int - 1;
    assert(s.index(s.len() - suffix.len() + k) == suffix.index(k));
}

proof fn last_char_determines_classification(s: Seq<char>)
    requires
        valid_sentence(s),
        s.len() >= 1,
    ensures
        s.index(s.len() as int - 1) == 'o' ==> ends_with(s, po_seq()),
        s.index(s.len() as int - 1) == 'u' ==> (ends_with(s, desu_seq()) || ends_with(s, masu_seq())),
        (s.index(s.len() as int - 1) != 'o' && s.index(s.len() as int - 1) != 'u') ==> ends_with(s, mnida_seq()),
{
    // Each suffix has a unique last character:
    // po -> 'o', desu -> 'u', masu -> 'u', mnida -> 'a'
    if ends_with(s, po_seq()) {
        ends_with_last_char(s, po_seq());
        // po_seq().index(1) == 'o'
    }
    if ends_with(s, desu_seq()) {
        ends_with_last_char(s, desu_seq());
        // desu_seq().index(3) == 'u'
    }
    if ends_with(s, masu_seq()) {
        ends_with_last_char(s, masu_seq());
        // masu_seq().index(3) == 'u'
    }
    if ends_with(s, mnida_seq()) {
        ends_with_last_char(s, mnida_seq());
        // mnida_seq().index(4) == 'a'
    }
}

proof fn valid_sentence_len_ge_2(s: Seq<char>)
    requires valid_sentence(s),
    ensures s.len() >= 2,
{
    // All suffixes have length >= 2, and ends_with requires s.len() >= suffix.len()
    // po_seq().len() == 2, desu_seq().len() == 4, masu_seq().len() == 4, mnida_seq().len() == 5
}

proof fn classify_all_step(sentences: Seq<Seq<char>>, i: int)
    requires
        0 <= i < sentences.len(),
        forall|j: int| 0 <= j < sentences.len() ==> valid_sentence(#[trigger] sentences.index(j)),
    ensures
        classify_all(sentences.take(i + 1)) =~=
            classify_all(sentences.take(i)).push(classify_sentence(sentences.index(i))),
{
    let s = sentences.take(i + 1);
    assert(s.len() == i + 1);
    assert(s.take(s.len() as int - 1) =~= sentences.take(i));
    assert(s.index(s.len() as int - 1) == sentences.index(i));

    assert forall|j: int| 0 <= j < s.len() implies valid_sentence(#[trigger] s.index(j)) by {
        assert(s.index(j) == sentences.index(j));
    }
}

proof fn suffix_three_loop(sentences: Seq<Seq<char>>, idx: int) -> (results: Seq<Seq<char>>)
    requires
        0 <= idx <= sentences.len(),
        forall|i: int| 0 <= i < sentences.len() ==> valid_sentence(#[trigger] sentences.index(i)),
    ensures
        results =~= classify_all(sentences.take(sentences.len() as int)),
    decreases sentences.len() - idx,
{
    if idx == sentences.len() {
        classify_all(sentences.take(idx))
    } else {
        let s = sentences.index(idx);
        assert(valid_sentence(s));

        valid_sentence_len_ge_2(s);
        last_char_determines_classification(s);
        classify_all_step(sentences, idx);

        suffix_three_loop(sentences, idx + 1)
    }
}

proof fn suffix_three(sentences: Seq<Seq<char>>) -> (results: Seq<Seq<char>>)
    requires
        forall|i: int| 0 <= i < sentences.len() ==> valid_sentence(#[trigger] sentences.index(i)),
    ensures
        results =~= classify_all(sentences),
{
    assert(sentences.take(sentences.len() as int) =~= sentences);
    suffix_three_loop(sentences, 0)
}

} // verus!

fn main() {}

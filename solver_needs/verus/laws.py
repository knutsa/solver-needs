"""The nine sequence laws of the AX probe for Verus.

Each law is a ``broadcast proof fn`` in vstd style with an explicit
trigger, proved by extensional equality. The probe appends a module with
the one law to the stripped program and brings it into scope with
``broadcast use`` directly after ``verus! {``; laws are never combined.
"""

LAWS: dict[str, str] = {
    "subrange-full": """
    pub broadcast proof fn ax<A>(s: Seq<A>)
        ensures #[trigger] s.subrange(0, s.len() as int) == s
    { assert(s.subrange(0, s.len() as int) =~= s); }
""",
    "push-subrange": """
    pub broadcast proof fn ax<A>(s: Seq<A>, x: A, i: int, j: int)
        ensures
            0 <= i <= j <= s.len() ==> #[trigger] s.push(x).subrange(i, j) == s.subrange(i, j),
            i == 0 && j == s.len() ==> s.push(x).subrange(i, j) == s,
    {
        if 0 <= i <= j <= s.len() {
            assert(s.push(x).subrange(i, j) =~= s.subrange(i, j));
            if i == 0 && j == s.len() { assert(s.subrange(i, j) =~= s); }
        }
    }
""",
    "subrange-subrange": """
    pub broadcast proof fn ax<A>(s: Seq<A>, i: int, j: int, k: int, l: int)
        ensures
            0 <= i <= j <= s.len() && 0 <= k <= l <= j - i
                ==> #[trigger] s.subrange(i, j).subrange(k, l) == s.subrange(i + k, i + l),
    {
        if 0 <= i <= j <= s.len() && 0 <= k <= l <= j - i {
            assert(s.subrange(i, j).subrange(k, l) =~= s.subrange(i + k, i + l));
        }
    }
""",
    "split-concat": """
    pub broadcast proof fn ax<A>(s: Seq<A>, i: int, j: int, k: int)
        ensures
            0 <= i <= j <= k <= s.len()
                ==> #[trigger] s.subrange(i, j).add(s.subrange(j, k)) == s.subrange(i, k),
            i == 0 && j <= k && k == s.len() && 0 <= j
                ==> s.subrange(i, j).add(s.subrange(j, k)) == s,
    {
        if 0 <= i <= j <= k <= s.len() {
            assert(s.subrange(i, j).add(s.subrange(j, k)) =~= s.subrange(i, k));
            if i == 0 && k == s.len() { assert(s.subrange(i, k) =~= s); }
        }
    }
""",
    "add-subrange": """
    pub broadcast proof fn ax<A>(a: Seq<A>, b: Seq<A>, i: int, j: int)
        ensures
            0 <= i <= j <= a.len() ==> #[trigger] a.add(b).subrange(i, j) == a.subrange(i, j),
            i == 0 && j == a.len() ==> a.add(b).subrange(i, j) == a,
            a.len() <= i <= j <= a.len() + b.len()
                ==> a.add(b).subrange(i, j) == b.subrange(i - a.len(), j - a.len()),
            i == a.len() && j == a.len() + b.len() ==> a.add(b).subrange(i, j) == b,
    {
        if 0 <= i <= j <= a.len() {
            assert(a.add(b).subrange(i, j) =~= a.subrange(i, j));
            if i == 0 && j == a.len() { assert(a.subrange(i, j) =~= a); }
        }
        if a.len() <= i <= j <= a.len() + b.len() {
            assert(a.add(b).subrange(i, j) =~= b.subrange(i - a.len(), j - a.len()));
            if i == a.len() && j == a.len() + b.len() {
                assert(b.subrange(i - a.len(), j - a.len()) =~= b);
            }
        }
    }
""",
    "subrange-push": """
    pub broadcast proof fn ax<A>(s: Seq<A>, i: int, j: int)
        ensures
            0 <= i <= j < s.len()
                ==> #[trigger] s.subrange(i, j).push(s[j]) == s.subrange(i, j + 1),
    {
        if 0 <= i <= j < s.len() {
            assert(s.subrange(i, j).push(s[j]) =~= s.subrange(i, j + 1));
        }
    }
""",
    "add-empty": """
    pub broadcast proof fn ax<A>(s: Seq<A>)
        ensures
            #[trigger] s.add(Seq::<A>::empty()) == s,
            #[trigger] Seq::<A>::empty().add(s) == s,
    {
        assert(s.add(Seq::<A>::empty()) =~= s);
        assert(Seq::<A>::empty().add(s) =~= s);
    }
""",
    "subrange-empty": """
    pub broadcast proof fn ax<A>(s: Seq<A>, i: int)
        ensures 0 <= i <= s.len() ==> #[trigger] s.subrange(i, i) == Seq::<A>::empty(),
    {
        if 0 <= i <= s.len() { assert(s.subrange(i, i) =~= Seq::<A>::empty()); }
    }
""",
    "add-assoc": """
    pub broadcast proof fn ax<A>(a: Seq<A>, b: Seq<A>, c: Seq<A>)
        ensures #[trigger] a.add(b).add(c) == a.add(b.add(c)),
    {
        assert(a.add(b).add(c) =~= a.add(b.add(c)));
    }
""",
}


def with_law(text: str, name: str) -> str:
    """``text`` plus a module holding law ``name``, brought into scope with ``broadcast use``."""
    text = text.replace("verus! {", "verus! {\nbroadcast use seq_laws::ax;\n", 1)
    return (
        text
        + "\nmod seq_laws {\n    use vstd::prelude::*;\n    verus! {"
        + LAWS[name]
        + "    }\n}\n"
    )

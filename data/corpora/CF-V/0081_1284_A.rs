use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

verus! {

// Ghost function: cyclic index for a year within a given period
spec fn cyclic_index(year: int, period: int) -> int
    recommends year >= 1, period > 0
{
    (year - 1) % period
}

// Proof that cyclic_index is in range [0, period)
proof fn lemma_cyclic_index_bounds(year: int, period: int)
    requires
        year >= 1,
        period > 0,
    ensures
        0 <= cyclic_index(year, period) < period,
{
    lemma_mod_bound(year - 1, period);
}

// Ghost function: GapjaName - concatenation of cyclic selections from s and t
spec fn gapja_name(year: int, s: Seq<Seq<char>>, t: Seq<Seq<char>>) -> Seq<char>
    recommends
        year >= 1,
        s.len() > 0,
        t.len() > 0,
{
    s[cyclic_index(year, s.len() as int)].add(t[cyclic_index(year, t.len() as int)])
}

// Helper: copy a Vec<char> to a new Vec<char>
fn clone_vec_char(v: &Vec<char>) -> (result: Vec<char>)
    ensures result@ =~= v@,
{
    let mut result: Vec<char> = Vec::new();
    let vlen = v.len();
    let mut k: usize = 0;
    while k < vlen
        invariant
            vlen == v@.len(),
            0 <= k <= vlen,
            result@.len() == k as int,
            result@ =~= v@.take(k as int),
        decreases vlen - k,
    {
        result.push(v[k]);
        assert(v@.take((k + 1) as int).drop_last() =~= v@.take(k as int));
        k = k + 1;
    }
    assert(v@.take(vlen as int) =~= v@);
    result
}

// Helper: concatenate two Vec<char>
fn concat_vec_char(a: &Vec<char>, b: &Vec<char>) -> (result: Vec<char>)
    ensures result@ =~= a@.add(b@),
{
    let mut result = clone_vec_char(a);
    let alen = a.len();
    let blen = b.len();
    let mut k: usize = 0;
    while k < blen
        invariant
            alen == a@.len(),
            blen == b@.len(),
            0 <= k <= blen,
            result@.len() == alen + k as int,
            result@ =~= a@.add(b@.take(k as int)),
        decreases blen - k,
    {
        result.push(b[k]);
        assert(b@.take((k + 1) as int).drop_last() =~= b@.take(k as int));
        assert(a@.add(b@.take((k + 1) as int)) =~= a@.add(b@.take(k as int)).push(b@[k as int]));
        k = k + 1;
    }
    assert(b@.take(blen as int) =~= b@);
    result
}

// Main method: process queries and return results
fn new_year_naming(
    n: usize,
    m: usize,
    s: &Vec<Vec<char>>,
    t: &Vec<Vec<char>>,
    queries: &Vec<usize>,
) -> (results: Vec<Vec<char>>)
    requires
        n > 0 && m > 0,
        s@.len() == n,
        t@.len() == m,
        forall|i: int| 0 <= i < queries@.len() ==> queries@[i] >= 1,
    ensures
        results@.len() == queries@.len(),
        forall|i: int|
            #![trigger results@[i]]
            0 <= i < queries@.len() ==> results@[i]@ =~= gapja_name(
                queries@[i] as int,
                s@.map(|_idx, v: Vec<char>| v@),
                t@.map(|_idx, v: Vec<char>| v@),
            ),
{
    let mut results: Vec<Vec<char>> = Vec::new();
    let ghost s_spec: Seq<Seq<char>> = s@.map(|_idx, v: Vec<char>| v@);
    let ghost t_spec: Seq<Seq<char>> = t@.map(|_idx, v: Vec<char>| v@);

    let q_len = queries.len();
    let mut i: usize = 0;
    while i < q_len
        invariant
            q_len == queries@.len(),
            0 <= i <= q_len,
            results@.len() == i as int,
            n > 0 && m > 0,
            s@.len() == n,
            t@.len() == m,
            s_spec == s@.map(|_idx, v: Vec<char>| v@),
            t_spec == t@.map(|_idx, v: Vec<char>| v@),
            s_spec.len() == n,
            t_spec.len() == m,
            forall|j: int| 0 <= j < queries@.len() ==> queries@[j] >= 1,
            forall|j: int|
                #![trigger results@[j]]
                0 <= j < i ==> results@[j]@ =~= gapja_name(
                    queries@[j] as int,
                    s_spec,
                    t_spec,
                ),
        decreases q_len - i,
    {
        let qi: usize = queries[i];
        assert(qi >= 1);
        let x: usize = qi - 1;

        // x % n and x % m are the cyclic indices
        let si: usize = x % n;
        let ti: usize = x % m;

        proof {
            lemma_cyclic_index_bounds(qi as int, n as int);
            lemma_cyclic_index_bounds(qi as int, m as int);
            // Connect runtime % to spec cyclic_index
            assert(si as int == (x as int) % (n as int));
            assert(cyclic_index(qi as int, n as int) == ((qi as int) - 1) % (n as int));
            assert(x as int == (qi as int) - 1);
            assert(si as int == cyclic_index(qi as int, n as int));
            assert(ti as int == cyclic_index(qi as int, m as int));
        }

        let combined = concat_vec_char(&s[si], &t[ti]);

        proof {
            // combined@ =~= s[si]@.add(t[ti]@)
            // s_spec[cyclic_index(qi, n)] = s@[si]@ by map definition
            let ci_s = cyclic_index(qi as int, n as int);
            let ci_t = cyclic_index(qi as int, m as int);
            assert(ci_s == si as int);
            assert(ci_t == ti as int);
            assert(s_spec[ci_s] =~= s@[si as int]@);
            assert(t_spec[ci_t] =~= t@[ti as int]@);
            assert(combined@ =~= s@[si as int]@.add(t@[ti as int]@));
            assert(combined@ =~= s_spec[ci_s].add(t_spec[ci_t]));
            assert(combined@ =~= gapja_name(qi as int, s_spec, t_spec));
        }

        results.push(combined);

        proof {
            assert(results@[i as int]@ =~= gapja_name(queries@[i as int] as int, s_spec, t_spec));
        }

        i = i + 1;
    }
    results
}

fn main() {}

} // verus!

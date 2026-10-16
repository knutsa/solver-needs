use vstd::prelude::*;

verus! {

spec fn valid_matrix(M: Seq<Seq<char>>, n: int) -> bool {
    n >= 0 &&
    M.len() == n &&
    forall|i: int| 0 <= i < n ==> (#[trigger] M[i]).len() == n
}

spec fn is_cross_at(M: Seq<Seq<char>>, n: int, a: int, b: int) -> bool
    recommends valid_matrix(M, n), 0 <= a < n, 0 <= b < n,
{
    1 <= a <= n - 2 &&
    1 <= b <= n - 2 &&
    M[a][b] == 'X' &&
    M[a - 1][b - 1] == 'X' &&
    M[a - 1][b + 1] == 'X' &&
    M[a + 1][b - 1] == 'X' &&
    M[a + 1][b + 1] == 'X'
}

// Count crosses in a single row `a`, for columns in [col..n-1)
spec fn cross_count_row(M: Seq<Seq<char>>, n: int, a: int, col: int) -> int
    recommends valid_matrix(M, n), 1 <= a <= n - 2, 1 <= col,
    decreases (if n - 1 - col > 0 { n - 1 - col } else { 0 }),
{
    if col >= n - 1 {
        0int
    } else {
        (if is_cross_at(M, n, a, col) { 1int } else { 0int })
            + cross_count_row(M, n, a, col + 1)
    }
}

// Count crosses for rows in [row..n-1)
spec fn cross_count_from(M: Seq<Seq<char>>, n: int, row: int) -> int
    recommends valid_matrix(M, n), 1 <= row,
    decreases (if n - 1 - row > 0 { n - 1 - row } else { 0 }),
{
    if row >= n - 1 {
        0int
    } else {
        cross_count_row(M, n, row, 1) + cross_count_from(M, n, row + 1)
    }
}

spec fn cross_count(M: Seq<Seq<char>>, n: int) -> int
    recommends valid_matrix(M, n),
{
    if n < 3 {
        0int
    } else {
        cross_count_from(M, n, 1)
    }
}

spec fn vec_to_seq(M: &Vec<Vec<char>>) -> Seq<Seq<char>> {
    M@.map_values(|v: Vec<char>| v@)
}

proof fn lemma_cross_count_row_nonneg(M: Seq<Seq<char>>, n: int, a: int, col: int)
    requires
        valid_matrix(M, n),
        1 <= a <= n - 2,
        1 <= col,
    ensures
        cross_count_row(M, n, a, col) >= 0,
    decreases (if n - 1 - col > 0 { n - 1 - col } else { 0 }),
{
    if col >= n - 1 {
    } else {
        lemma_cross_count_row_nonneg(M, n, a, col + 1);
    }
}

proof fn lemma_cross_count_from_nonneg(M: Seq<Seq<char>>, n: int, row: int)
    requires
        valid_matrix(M, n),
        1 <= row,
    ensures
        cross_count_from(M, n, row) >= 0,
    decreases (if n - 1 - row > 0 { n - 1 - row } else { 0 }),
{
    if row >= n - 1 {
    } else {
        lemma_cross_count_row_nonneg(M, n, row, 1);
        lemma_cross_count_from_nonneg(M, n, row + 1);
    }
}

proof fn lemma_cross_count_row_upper(M: Seq<Seq<char>>, n: int, a: int, col: int)
    requires
        valid_matrix(M, n),
        1 <= a <= n - 2,
        1 <= col,
    ensures
        cross_count_row(M, n, a, col) <= (if col < n - 1 { n - 1 - col } else { 0int }),
    decreases (if n - 1 - col > 0 { n - 1 - col } else { 0 }),
{
    if col >= n - 1 {
    } else {
        lemma_cross_count_row_upper(M, n, a, col + 1);
    }
}

proof fn lemma_cross_count_from_upper(M: Seq<Seq<char>>, n: int, row: int)
    requires
        valid_matrix(M, n),
        n >= 3,
        1 <= row,
    ensures
        cross_count_from(M, n, row) <= (if row < n - 1 { (n - 1 - row) * (n - 2) } else { 0int }),
    decreases (if n - 1 - row > 0 { n - 1 - row } else { 0 }),
{
    if row >= n - 1 {
    } else {
        lemma_cross_count_row_upper(M, n, row, 1);
        lemma_cross_count_row_nonneg(M, n, row, 1);
        lemma_cross_count_from_upper(M, n, row + 1);
        lemma_cross_count_from_nonneg(M, n, row + 1);
        let row_ub = cross_count_row(M, n, row, 1);
        let from_ub = cross_count_from(M, n, row + 1);
        assert(row_ub <= n - 2);
        assert(row_ub >= 0);
        assert(from_ub >= 0);
        if row + 1 < n - 1 {
            assert(from_ub <= (n - 2 - row) * (n - 2));
            assert((n - 2) + (n - 2 - row) * (n - 2) == (n - 1 - row) * (n - 2)) by (nonlinear_arith)
                requires n >= 3, 1 <= row, row + 1 < n - 1;
        } else {
            assert(from_ub <= 0);
            assert(row >= n - 2);
            assert(row < n - 1);
            // row == n - 2, so (n - 1 - row) * (n - 2) == 1 * (n - 2) == n - 2
            assert((n - 1 - row) * (n - 2) >= n - 2) by (nonlinear_arith)
                requires row == n - 2, n >= 3;
        }
    }
}

fn count_crosses(n: i64, M: &Vec<Vec<char>>) -> (count: i64)
    requires
        n >= 0,
        n < 10000,
        M@.len() == n,
        forall|i: int| 0 <= i < n ==> (#[trigger] M@[i])@.len() == n,
    ensures
        count == cross_count(vec_to_seq(M), n as int),
{
    let ghost m_spec: Seq<Seq<char>> = vec_to_seq(M);

    proof {
        assert(m_spec.len() == n);
        assert forall|i: int| 0 <= i < n implies (#[trigger] m_spec[i]).len() == n by {
            assert(M@[i]@.len() == n);
        }
    }

    let mut count: i64 = 0;

    if n < 3 {
        return count;
    }

    proof {
        lemma_cross_count_from_upper(m_spec, n as int, 1);
        lemma_cross_count_from_nonneg(m_spec, n as int, 1);
    }

    let mut a: i64 = 1;

    while a < n - 1
        invariant
            1 <= a <= n - 1,
            n >= 3,
            n < 10000,
            valid_matrix(m_spec, n as int),
            m_spec === vec_to_seq(M),
            M@.len() == n,
            forall|i: int| 0 <= i < n ==> (#[trigger] M@[i])@.len() == n,
            count == cross_count_from(m_spec, n as int, 1) - cross_count_from(m_spec, n as int, a as int),
            cross_count_from(m_spec, n as int, 1) <= (n - 2) * (n - 2),
            cross_count_from(m_spec, n as int, 1) >= 0,
            cross_count_from(m_spec, n as int, a as int) >= 0,
            cross_count_from(m_spec, n as int, a as int) <= cross_count_from(m_spec, n as int, 1),
        decreases n - 1 - a,
    {
        let mut b: i64 = 1;
        let mut row_count: i64 = 0;

        proof {
            lemma_cross_count_row_nonneg(m_spec, n as int, a as int, 1);
            lemma_cross_count_row_upper(m_spec, n as int, a as int, 1);
        }

        while b < n - 1
            invariant
                1 <= b <= n - 1,
                1 <= a <= n - 2,
                n >= 3,
                n < 10000,
                valid_matrix(m_spec, n as int),
                m_spec === vec_to_seq(M),
                M@.len() == n,
                forall|i: int| 0 <= i < n ==> (#[trigger] M@[i])@.len() == n,
                row_count == cross_count_row(m_spec, n as int, a as int, 1) - cross_count_row(m_spec, n as int, a as int, b as int),
                cross_count_row(m_spec, n as int, a as int, 1) <= n - 2,
                cross_count_row(m_spec, n as int, a as int, b as int) >= 0,
            decreases n - 1 - b,
        {
            proof {
                assert(m_spec[a as int] === M@[a as int]@);
                assert(m_spec[(a-1) as int] === M@[(a-1) as int]@);
                assert(m_spec[(a+1) as int] === M@[(a+1) as int]@);
            }

            if M[a as usize][b as usize] == 'X'
                && M[(a - 1) as usize][(b - 1) as usize] == 'X'
                && M[(a - 1) as usize][(b + 1) as usize] == 'X'
                && M[(a + 1) as usize][(b - 1) as usize] == 'X'
                && M[(a + 1) as usize][(b + 1) as usize] == 'X'
            {
                proof {
                    assert(is_cross_at(m_spec, n as int, a as int, b as int));
                    assert(cross_count_row(m_spec, n as int, a as int, b as int)
                        == 1 + cross_count_row(m_spec, n as int, a as int, (b + 1) as int));
                    lemma_cross_count_row_nonneg(m_spec, n as int, a as int, (b + 1) as int);
                }
                row_count = row_count + 1;
            } else {
                proof {
                    assert(!is_cross_at(m_spec, n as int, a as int, b as int));
                    assert(cross_count_row(m_spec, n as int, a as int, b as int)
                        == cross_count_row(m_spec, n as int, a as int, (b + 1) as int));
                }
            }
            b = b + 1;
        }

        proof {
            assert(cross_count_row(m_spec, n as int, a as int, (n - 1) as int) == 0);
            assert(row_count == cross_count_row(m_spec, n as int, a as int, 1));
            assert(cross_count_from(m_spec, n as int, a as int)
                == cross_count_row(m_spec, n as int, a as int, 1)
                   + cross_count_from(m_spec, n as int, (a + 1) as int));
            lemma_cross_count_from_nonneg(m_spec, n as int, (a + 1) as int);
            // cross_count_from(a+1) = cross_count_from(a) - row_count
            // cross_count_from(a+1) <= cross_count_from(a) <= cross_count_from(1)
            // count + row_count = cross_count_from(1) - cross_count_from(a) + row_count
            //                   = cross_count_from(1) - cross_count_from(a+1)
            // This is >= 0 and <= cross_count_from(1) <= (n-2)*(n-2)
        }

        assert(count >= 0) by {
            // count = cross_count_from(1) - cross_count_from(a)
            // cross_count_from(a) <= cross_count_from(1)
        }
        assert(row_count >= 0) by {
            // row_count = cross_count_row(a, 1) - 0 = cross_count_row(a, 1) >= 0
        }
        assert(count + row_count <= (n - 2) * (n - 2)) by {
            // count + row_count = cross_count_from(1) - cross_count_from(a+1)
            // <= cross_count_from(1) <= (n-2)*(n-2)
        }
        assert((n as int - 2) * (n as int - 2) < 100_000_000int) by (nonlinear_arith)
            requires 3 <= n, n < 10000int;
        count = count + row_count;
        a = a + 1;
    }

    proof {
        assert(cross_count_from(m_spec, n as int, (n - 1) as int) == 0);
    }

    count
}

fn main() {}

} // verus!

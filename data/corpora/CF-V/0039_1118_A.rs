use vstd::prelude::*;

verus! {

spec fn IsValidPurchase(ones: int, twos: int, n: int) -> bool {
    ones >= 0 && twos >= 0 && ones + 2 * twos == n
}

spec fn PurchaseCost(ones: int, twos: int, a: int, b: int) -> int {
    ones * a + twos * b
}

spec fn MinCost(n: int, a: int, b: int) -> int {
    let allOnesCost = PurchaseCost(n, 0, a, b);
    let maxTwosCost = PurchaseCost(n % 2, n / 2, a, b);
    if allOnesCost <= maxTwosCost { allOnesCost } else { maxTwosCost }
}

#[verifier::loop_isolation(false)]
fn WaterBuying(queries: &Vec<(i64, i64, i64)>) -> (results: Vec<i64>)
    requires
        forall|i: int| 0 <= i < queries@.len() ==>
            queries@[i].0 >= 0 && queries@[i].0 <= 1_000_000_000 &&
            queries@[i].1 >= 0 && queries@[i].1 <= 1_000_000_000 &&
            queries@[i].2 >= 0 && queries@[i].2 <= 1_000_000_000,
    ensures
        results@.len() == queries@.len(),
        forall|i: int| 0 <= i < queries@.len() ==>
            results@[i] as int == MinCost(
                queries@[i].0 as int,
                queries@[i].1 as int,
                queries@[i].2 as int,
            ),
{
    let mut results: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < queries.len()
        invariant
            0 <= i <= queries@.len(),
            results@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==>
                results@[j] as int == MinCost(
                    queries@[j].0 as int,
                    queries@[j].1 as int,
                    queries@[j].2 as int,
                ),
        decreases queries@.len() - i,
    {
        let (n, a, b) = queries[i];
        let two = 2 * a;
        let m = if two < b { two } else { b };

        proof {
            let n_int = n as int;
            let a_int = a as int;
            let m_int = m as int;

            assert(n_int / 2 >= 0 && n_int / 2 <= 500_000_000) by(nonlinear_arith)
                requires 0 <= n_int <= 1_000_000_000;
            assert(0 <= m_int <= 2_000_000_000);
            assert((n_int / 2) * m_int >= 0 && (n_int / 2) * m_int <= 1_000_000_000_000_000_000int) by(nonlinear_arith)
                requires n_int / 2 >= 0, n_int / 2 <= 500_000_000, m_int >= 0, m_int <= 2_000_000_000;
            assert(n_int % 2 >= 0 && n_int % 2 <= 1) by(nonlinear_arith)
                requires n_int >= 0;
            assert((n_int % 2) * a_int >= 0 && (n_int % 2) * a_int <= 1_000_000_000) by(nonlinear_arith)
                requires n_int % 2 >= 0, n_int % 2 <= 1, a_int >= 0, a_int <= 1_000_000_000;
        }

        let ans = (n / 2) * m + (n % 2) * a;

        proof {
            let n_int = n as int;
            let a_int = a as int;
            let b_int = b as int;
            let m_int = m as int;
            let ans_int = ans as int;

            assert(n_int >= 0);

            assert((n_int / 2) * 2 + (n_int % 2) == n_int) by(nonlinear_arith)
                requires n_int >= 0;

            assert(n_int / 2 >= 0) by(nonlinear_arith)
                requires n_int >= 0;

            assert(n_int % 2 >= 0) by(nonlinear_arith)
                requires n_int >= 0;

            assert(PurchaseCost(n_int, 0, a_int, b_int) == n_int * a_int);
            assert(PurchaseCost(n_int % 2, n_int / 2, a_int, b_int) == (n_int % 2) * a_int + (n_int / 2) * b_int);

            if two < b {
                assert(m_int == 2 * a_int);

                assert(ans_int == n_int * a_int) by(nonlinear_arith)
                    requires
                        ans_int == (n_int / 2) * m_int + (n_int % 2) * a_int,
                        m_int == 2 * a_int,
                        (n_int / 2) * 2 + (n_int % 2) == n_int,
                ;

                assert(n_int * a_int <= (n_int % 2) * a_int + (n_int / 2) * b_int) by(nonlinear_arith)
                    requires
                        (n_int / 2) * 2 + (n_int % 2) == n_int,
                        n_int / 2 >= 0,
                        2 * a_int < b_int,
                ;
            } else {
                assert(m_int == b_int);

                assert(ans_int == (n_int / 2) * b_int + (n_int % 2) * a_int) by(nonlinear_arith)
                    requires
                        ans_int == (n_int / 2) * m_int + (n_int % 2) * a_int,
                        m_int == b_int,
                ;

                assert((n_int % 2) * a_int + (n_int / 2) * b_int <= n_int * a_int) by(nonlinear_arith)
                    requires
                        (n_int / 2) * 2 + (n_int % 2) == n_int,
                        n_int / 2 >= 0,
                        2 * a_int >= b_int,
                ;
            }

            assert(ans_int == MinCost(n_int, a_int, b_int));
        }

        results.push(ans);
        i += 1;
    }
    results
}

fn main() {}

} // verus!
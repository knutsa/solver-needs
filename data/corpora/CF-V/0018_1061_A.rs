use vstd::prelude::*;

verus! {

spec fn Sum(a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        Sum(a.take(a.len() - 1)) + a[a.len() - 1]
    }
}

spec fn AllValid(coins: Seq<int>, n: int) -> bool {
    forall|i: int| 0 <= i < coins.len() ==> 1 <= coins[i] && coins[i] <= n
}

spec fn IsValidSelection(coins: Seq<int>, n: int, S: int) -> bool {
    coins.len() >= 1 && AllValid(coins, n) && Sum(coins) == S
}

spec fn Achievable(k: int, n: int, S: int) -> bool {
    k >= 1 && n >= 1 && k <= S && S <= k * n
}

spec fn Witness(k: int, n: int, S: int) -> Seq<int> {
    if k >= 1 && n >= 1 && k <= S && S <= k * n {
        Seq::new(k as nat, |i: int| if i < k - 1 { n } else { S - (k - 1) * n })
    } else {
        Seq::empty()
    }
}

fn Coins(n: i64, S: i64) -> (min_coins: i64)
    requires
        n >= 1,
        S >= 1,
    ensures
        Achievable(min_coins as int, n as int, S as int),
        forall|k: int| 1 <= k && k < min_coins as int ==> !Achievable(k, n as int, S as int),
{
    let min_coins: i64 = (S - 1) / n + 1;
    let q: i64 = (S - 1) / n;
    let r: i64 = (S - 1) % n;

    proof {
        let q_int = q as int;
        let r_int = r as int;
        let n_int = n as int;
        let s_int = S as int;
        let mc_int = min_coins as int;

        // Properties of integer division: S - 1 == q * n + r, 0 <= r < n
        assert(s_int - 1 == q_int * n_int + r_int) by(nonlinear_arith)
            requires
                s_int >= 1,
                n_int >= 1,
                q_int == (s_int - 1) / n_int,
                r_int == (s_int - 1) % n_int,
        {}

        assert(0 <= r_int < n_int) by(nonlinear_arith)
            requires
                s_int >= 1,
                n_int >= 1,
                r_int == (s_int - 1) % n_int,
        {}

        assert(mc_int == q_int + 1);

        // 1. min_coins >= 1
        assert(mc_int >= 1) by(nonlinear_arith)
            requires
                s_int >= 1,
                n_int >= 1,
                q_int == (s_int - 1) / n_int,
                mc_int == q_int + 1,
        {}

        // 2. min_coins <= S: since q*(n-1) >= 0 and r >= 0
        assert(q_int >= 0) by(nonlinear_arith)
            requires
                s_int >= 1,
                n_int >= 1,
                q_int == (s_int - 1) / n_int,
        {}

        assert(q_int * (n_int - 1) >= 0) by(nonlinear_arith)
            requires
                q_int >= 0,
                n_int >= 1,
        {}

        // mc = q + 1, S = q*n + r + 1, so S - mc = q*n + r + 1 - q - 1 = q*(n-1) + r >= 0
        assert(mc_int <= s_int) by(nonlinear_arith)
            requires
                s_int - 1 == q_int * n_int + r_int,
                r_int >= 0,
                q_int >= 0,
                n_int >= 1,
                mc_int == q_int + 1,
        {}

        // 3. S <= min_coins * n: since r + 1 <= n
        assert(r_int + 1 <= n_int);
        // S = q*n + r + 1 <= q*n + n = (q+1)*n = mc*n
        assert(s_int <= mc_int * n_int) by(nonlinear_arith)
            requires
                s_int - 1 == q_int * n_int + r_int,
                r_int + 1 <= n_int,
                mc_int == q_int + 1,
        {}

        // Prove minimality: for k < min_coins, k*n < S so !Achievable
        assert forall|k: int| 1 <= k && k < mc_int implies !Achievable(k, n_int, s_int) by {
            // k <= q, so k*n <= q*n <= S - 1, so S > k*n
            assert(k <= q_int);
            assert(k * n_int <= q_int * n_int) by(nonlinear_arith)
                requires
                    k <= q_int,
                    n_int >= 1,
            {}
            assert(q_int * n_int <= s_int - 1) by(nonlinear_arith)
                requires
                    s_int - 1 == q_int * n_int + r_int,
                    r_int >= 0,
            {}
            assert(s_int > k * n_int);
        }
    }
    min_coins
}

fn main() {}

} // verus!

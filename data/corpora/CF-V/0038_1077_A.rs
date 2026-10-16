use vstd::prelude::*;

verus! {

spec fn FrogPosition(a: int, b: int, k: nat) -> int
    decreases k
{
    if k == 0 {
        0
    } else if (k - 1) % 2 == 0 {
        FrogPosition(a, b, (k - 1) as nat) + a
    } else {
        FrogPosition(a, b, (k - 1) as nat) - b
    }
}

spec fn ClosedForm(a: int, b: int, k: nat) -> int {
    (k as int / 2) * a - (k as int / 2) * b + (if k as int % 2 == 1 { a } else { 0 })
}

proof fn frog_position_unfold_even(a: int, b: int, k: nat)
    requires k >= 1, (k - 1) % 2 == 0
    ensures FrogPosition(a, b, k) == FrogPosition(a, b, (k - 1) as nat) + a
{
    reveal_with_fuel(FrogPosition, 2);
}

proof fn frog_position_unfold_odd(a: int, b: int, k: nat)
    requires k >= 1, (k - 1) % 2 != 0
    ensures FrogPosition(a, b, k) == FrogPosition(a, b, (k - 1) as nat) - b
{
    reveal_with_fuel(FrogPosition, 2);
}

proof fn FrogPositionClosedForm(a: int, b: int, k: nat)
    ensures FrogPosition(a, b, k) == ClosedForm(a, b, k)
    decreases k
{
    if k == 0 {
        reveal_with_fuel(FrogPosition, 1);
        assert(FrogPosition(a, b, 0nat) == 0);
        assert(ClosedForm(a, b, 0nat) == 0);
        assert(FrogPosition(a, b, k) == ClosedForm(a, b, k));
    } else if k == 1 {
        reveal_with_fuel(FrogPosition, 3);
        assert(FrogPosition(a, b, 1nat) == FrogPosition(a, b, 0nat) + a);
        assert(FrogPosition(a, b, 0nat) == 0int);
        assert(1int / 2 == 0) by(nonlinear_arith);
        assert(0 * a == 0) by(nonlinear_arith);
        assert(0 * b == 0) by(nonlinear_arith);
        assert(1int % 2 == 1) by(nonlinear_arith);
        assert(ClosedForm(a, b, 1nat) == a);
        assert(FrogPosition(a, b, k) == ClosedForm(a, b, k));
    } else {
        let km1: nat = (k - 1) as nat;
        FrogPositionClosedForm(a, b, km1);
        // IH: FrogPosition(a, b, km1) == ClosedForm(a, b, km1)
        let ih_val = ClosedForm(a, b, km1);
        assert(FrogPosition(a, b, km1) == ih_val);

        if (k - 1) % 2 == 0 {
            frog_position_unfold_even(a, b, k);
            // FrogPosition(a,b,k) == FrogPosition(a,b,km1) + a == ih_val + a
            assert(FrogPosition(a, b, k) == ih_val + a);

            // Now show ih_val + a == ClosedForm(a, b, k)
            assert(((k as int) - 1) / 2 == (k as int) / 2) by(nonlinear_arith)
                requires k >= 2, ((k as int) - 1) % 2 == 0;
            assert((k as int) % 2 == 1) by(nonlinear_arith)
                requires ((k as int) - 1) % 2 == 0, k >= 2;
            // ih_val = ClosedForm(a,b,km1) = ((k-1)/2)*a - ((k-1)/2)*b + 0
            //        = (k/2)*a - (k/2)*b
            // ih_val + a = (k/2)*a - (k/2)*b + a = ClosedForm(a,b,k)
            let h = (k as int) / 2;
            assert(ih_val == h * a - h * b);
            assert(ClosedForm(a, b, k) == h * a - h * b + a);
            assert(ih_val + a == ClosedForm(a, b, k));
        } else {
            frog_position_unfold_odd(a, b, k);
            // FrogPosition(a,b,k) == FrogPosition(a,b,km1) - b == ih_val - b
            assert(FrogPosition(a, b, k) == ih_val - b);

            // Now show ih_val - b == ClosedForm(a, b, k)
            assert(((k as int) - 1) / 2 + 1 == (k as int) / 2) by(nonlinear_arith)
                requires k >= 2, ((k as int) - 1) % 2 != 0;
            assert((k as int) % 2 == 0) by(nonlinear_arith)
                requires ((k as int) - 1) % 2 != 0, k >= 2;
            assert(((k as int) - 1) % 2 == 1) by(nonlinear_arith)
                requires ((k as int) - 1) % 2 != 0, k >= 2;
            let h1 = ((k as int) - 1) / 2;
            let h2 = (k as int) / 2;
            assert(h1 + 1 == h2);
            // ih_val = ClosedForm(a,b,km1) = h1*a - h1*b + a
            assert(ih_val == h1 * a - h1 * b + a);
            // ih_val - b = h1*a - h1*b + a - b
            assert(h1 * a + a == (h1 + 1) * a) by(nonlinear_arith);
            assert(h1 * b + b == (h1 + 1) * b) by(nonlinear_arith);
            // = (h1+1)*a - (h1+1)*b = h2*a - h2*b = ClosedForm(a,b,k)
            assert(ClosedForm(a, b, k) == h2 * a - h2 * b);
            assert(ih_val - b == ClosedForm(a, b, k));
            assert(FrogPosition(a, b, k) == ClosedForm(a, b, k));
        }
        assert(FrogPosition(a, b, k) == ClosedForm(a, b, k));
    }
}

#[verifier::loop_isolation(false)]
fn FrogJumping(queries: &Vec<(i64, i64, i64)>) -> (results: Vec<i64>)
    requires
        forall|i: int| 0 <= i < queries@.len() ==> (#[trigger] queries@[i]).2 >= 0,
        forall|i: int| #![trigger queries@[i]]
            0 <= i < queries@.len() ==> {
                let q = queries@[i];
                let a = q.0 as int;
                let b = q.1 as int;
                let k = q.2 as int;
                let half = k / 2;
                &&& i64::MIN <= a * half
                &&& a * half <= i64::MAX
                &&& i64::MIN <= b * half
                &&& b * half <= i64::MAX
                &&& i64::MIN <= a * half - b * half
                &&& a * half - b * half <= i64::MAX
                &&& i64::MIN <= a * half - b * half + a
                &&& a * half - b * half + a <= i64::MAX
            },
    ensures
        results@.len() == queries@.len(),
        forall|i: int| 0 <= i < queries@.len() ==>
            (#[trigger] results@[i]) as int == FrogPosition(
                queries@[i].0 as int,
                queries@[i].1 as int,
                queries@[i].2 as nat,
            ),
{
    let mut results: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < queries.len()
        invariant
            0 <= i <= queries@.len(),
            results@.len() == i as int,
            forall|j: int| 0 <= j < i ==>
                (#[trigger] results@[j]) as int == FrogPosition(
                    queries@[j].0 as int,
                    queries@[j].1 as int,
                    queries@[j].2 as nat,
                ),
            forall|j: int| 0 <= j < queries@.len() ==> (#[trigger] queries@[j]).2 >= 0,
            forall|j: int| #![trigger queries@[j]]
                0 <= j < queries@.len() ==> {
                    let q = queries@[j];
                    let a = q.0 as int;
                    let b = q.1 as int;
                    let k = q.2 as int;
                    let half = k / 2;
                    &&& i64::MIN <= a * half
                    &&& a * half <= i64::MAX
                    &&& i64::MIN <= b * half
                    &&& b * half <= i64::MAX
                    &&& i64::MIN <= a * half - b * half
                    &&& a * half - b * half <= i64::MAX
                    &&& i64::MIN <= a * half - b * half + a
                    &&& a * half - b * half + a <= i64::MAX
                },
        decreases queries@.len() - i,
    {
        let (a, b, k) = queries[i];
        let half = k / 2;
        let mut ans: i64 = a * half - b * half;
        if k % 2 == 1 {
            ans = ans + a;
        }
        proof {
            FrogPositionClosedForm(a as int, b as int, k as nat);
            assert(a as int * (k as int / 2) == (k as int / 2) * (a as int)) by(nonlinear_arith);
            assert(b as int * (k as int / 2) == (k as int / 2) * (b as int)) by(nonlinear_arith);
        }
        results.push(ans);
        i = i + 1;
    }
    results
}

fn main() {}

} // verus!

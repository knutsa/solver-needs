use vstd::prelude::*;

verus! {

pub open spec fn min_spec(a: int, b: int) -> int {
    if a <= b { a } else { b }
}

pub open spec fn max_spec(a: int, b: int) -> int {
    if a >= b { a } else { b }
}

pub open spec fn divides(d: int, n: int) -> bool
    recommends d > 0
{
    n % d == 0
}

pub open spec fn is_gcd(g: int, a: int, b: int) -> bool
    recommends a > 0 && b > 0 && g > 0
{
    divides(g, a) && divides(g, b) &&
    forall|d: int| 1 <= d <= min_spec(a, b) ==> (divides(d, a) && divides(d, b)) ==> d <= g
}

pub open spec fn is_lcm(l: int, a: int, b: int) -> bool
    recommends a > 0 && b > 0 && l > 0
{
    divides(a, l) && divides(b, l) &&
    forall|m: int| 1 <= m <= l ==> (divides(a, m) && divides(b, m)) ==> l <= m
}

pub open spec fn valid_solution(a: int, b: int, x: int) -> bool {
    a > 0 && b > 0 && x > 0 &&
    exists|g: int| 1 <= g <= min_spec(a, b) && (
        exists|l: int| max_spec(a, b) <= l <= a * b && (
            #[trigger] is_gcd(g, a, b) && is_lcm(l, a, b) && g + l == x
        )
    )
}

proof fn div_mod_lemma(b: int, m: int)
    requires
        b > 0,
        1 <= m <= b,
        m % b == 0,
    ensures
        m == b,
{
    let q = m / b;
    assert(m == q * b + m % b) by(nonlinear_arith)
        requires m / b == q, b > 0, m == m
    {
    }
    assert(m == q * b);
    assert(q >= 1) by(nonlinear_arith)
        requires m >= 1, m == q * b, b > 0
    {
    }
    assert(q <= 1) by(nonlinear_arith)
        requires m <= b, m == q * b, b > 0
    {
    }
    assert(q == 1);
    assert(m == b) by(nonlinear_arith)
        requires q == 1, m == q * b
    {
    }
}

fn eh_ab_and_gcd(x: i64) -> (result: (i64, i64))
    requires
        x >= 2,
    ensures
        valid_solution(result.0 as int, result.1 as int, x as int),
{
    let a: i64 = 1;
    let b: i64 = x - 1;

    let ghost g: int = 1;
    let ghost l: int = (x - 1) as int;

    assert(divides(g, a as int));
    assert(divides(g, b as int));

    // GCD(1, x-1) = 1: any d dividing 1 must be <= 1
    assert(is_gcd(g, a as int, b as int)) by {
        assert(divides(g, a as int));
        assert(divides(g, b as int));
        assert forall|d: int| 1 <= d <= min_spec(a as int, b as int) implies
            (divides(d, a as int) && divides(d, b as int)) ==> d <= g
        by {
            // a == 1, so min_spec(1, b) == 1, so d == 1 == g
        }
    }

    // LCM(1, x-1) = x-1
    assert(divides(a as int, l));
    assert(divides(b as int, l));

    // For the LCM universally quantified part
    assert forall|m: int| 1 <= m <= l && divides(a as int, m) && divides(b as int, m) implies l <= m
    by {
        div_mod_lemma(b as int, m);
    }

    assert(is_lcm(l, a as int, b as int));
    assert(g + l == x as int);

    // Provide witnesses for the existentials
    assert(1 <= g <= min_spec(a as int, b as int));
    assert(max_spec(a as int, b as int) <= l <= (a as int) * (b as int));

    assert(valid_solution(a as int, b as int, x as int)) by {
        assert(is_gcd(g, a as int, b as int) && is_lcm(l, a as int, b as int) && g + l == x as int);
        assert(max_spec(a as int, b as int) <= l <= (a as int) * (b as int) &&
               is_gcd(g, a as int, b as int) && is_lcm(l, a as int, b as int) && g + l == x as int);
        assert(1 <= g <= min_spec(a as int, b as int) &&
               (exists|l2: int| max_spec(a as int, b as int) <= l2 <= (a as int) * (b as int) &&
                   is_gcd(g, a as int, b as int) && is_lcm(l2, a as int, b as int) && g + l2 == x as int));
    }

    (a, b)
}

fn main() {}

} // verus!

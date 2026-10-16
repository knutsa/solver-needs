use vstd::prelude::*;

verus! {

spec fn MeetAt(x: int, y: int, a: int, b: int, t: int) -> bool {
    t >= 1 && x + t * a == y - t * b
}

proof fn lemma_div_mod(z: int, c: int)
    requires c != 0
    ensures z == (z / c) * c + (z % c)
{
    assert(z == (z / c) * c + (z % c)) by(nonlinear_arith)
        requires c != 0;
}

proof fn lemma_mod_range(z: int, c: int)
    requires c > 0
    ensures 0 <= z % c < c
{
    assert(0 <= z % c < c) by(nonlinear_arith)
        requires c > 0;
}

proof fn nla_step(t_prime: int, c: int, z: int, q: int, r: int)
    requires
        t_prime >= 1,
        c > 0,
        r > 0,
        r < c,
        z == q * c + r,
        t_prime * c == z,
    ensures
        false
{
    // From t_prime * c == z == q * c + r
    // we get (t_prime - q) * c == r
    assert((t_prime - q) * c == r) by(nonlinear_arith)
        requires
            t_prime * c == q * c + r,
    ;
    if t_prime == q {
        assert(0 * c == 0) by(nonlinear_arith);
        // (t_prime - q) * c == 0 * c == 0 == r, but r > 0
        assert(false);
    } else if t_prime > q {
        // t_prime - q >= 1, so (t_prime - q) * c >= c > r, contradiction
        assert((t_prime - q) >= 1int);
        assert((t_prime - q) * c >= 1 * c) by(nonlinear_arith)
            requires
                t_prime - q >= 1,
                c > 0,
        ;
        assert(r >= c);
        assert(false);
    } else {
        // t_prime < q, so t_prime - q <= -1, so (t_prime - q) * c <= -c < 0 <= r
        assert(t_prime - q <= -1int);
        assert((t_prime - q) * c <= -1 * c) by(nonlinear_arith)
            requires
                t_prime - q <= -1,
                c > 0,
        ;
        assert(r <= -c);
        assert(false);
    }
}

fn TwoRabbits(x: i64, y: i64, a: i64, b: i64) -> (t: i64)
    requires
        x < y,
        a >= 1,
        b >= 1,
        // overflow safety
        i64::MIN < y - x,
        (y - x) < i64::MAX,
        a + b > 0,
        a + b < i64::MAX,
    ensures
        t == -1 || t >= 1,
        t >= 1 ==> MeetAt(x as int, y as int, a as int, b as int, t as int),
        t == -1 ==> forall|t_prime: int| t_prime >= 1 ==> !MeetAt(x as int, y as int, a as int, b as int, t_prime),
{
    let z = y - x;
    let c = a + b;
    if z % c != 0 {
        let ghost q = (z as int) / (c as int);
        let ghost r = (z as int) % (c as int);

        proof {
            lemma_div_mod(z as int, c as int);
            lemma_mod_range(z as int, c as int);
            assert(z as int == q * (c as int) + r);
            assert(r > 0);
            assert(r < c as int);
        }

        proof {
            assert forall|t_prime: int| t_prime >= 1 implies !MeetAt(x as int, y as int, a as int, b as int, t_prime) by {
                if MeetAt(x as int, y as int, a as int, b as int, t_prime) {
                    assert(x as int + t_prime * (a as int) == y as int - t_prime * (b as int));
                    // t_prime * a + t_prime * b == y - x == z
                    assert(t_prime * (a as int) + t_prime * (b as int) == (y - x) as int);
                    assert(t_prime * ((a as int) + (b as int)) == (z as int)) by(nonlinear_arith)
                        requires
                            t_prime * (a as int) + t_prime * (b as int) == (z as int),
                    ;
                    assert(t_prime * (c as int) == (z as int));
                    nla_step(t_prime, c as int, z as int, q, r);
                }
            }
        }
        -1i64
    } else {
        let t = z / c;
        proof {
            // z % c == 0, so z == t * c
            lemma_div_mod(z as int, c as int);
            assert((z as int) % (c as int) == 0int);
            assert((t as int) * (c as int) == (z as int));
            // t * (a + b) == y - x
            // t * a + t * b == y - x
            assert((t as int) * ((a as int) + (b as int)) == (y as int) - (x as int));
            assert((t as int) * (a as int) + (t as int) * (b as int) == (y as int) - (x as int)) by(nonlinear_arith)
                requires
                    (t as int) * ((a as int) + (b as int)) == (y as int) - (x as int),
            ;
            assert((x as int) + (t as int) * (a as int) == (y as int) - (t as int) * (b as int));

            // Need t >= 1: z > 0 and c > 0 so t = z/c >= 1
            assert((z as int) > 0);
            assert((c as int) > 0);
            // z >= c would give t >= 1, but z could be < c... wait, z % c == 0 and z > 0, c > 0
            // so z >= c, meaning t >= 1
            // Actually z could equal c in which case t = 1, or z = 2c giving t = 2, etc.
            // Since z > 0 and z % c == 0 and c > 0, the smallest z can be is c, so t >= 1.
            assert((t as int) >= 1) by(nonlinear_arith)
                requires
                    (t as int) * (c as int) == (z as int),
                    (z as int) > 0,
                    (c as int) > 0,
            ;
        }
        t
    }
}

fn main() {}

} // verus!

use vstd::prelude::*;
use vstd::arithmetic::div_mod::*;

verus! {

// ghost function Sum(a: seq<int>): int
spec fn sum_spec(a: Seq<int>) -> int
    decreases a.len(),
{
    if a.len() == 0 {
        0int
    } else {
        sum_spec(a.take(a.len() as int - 1)) + a[a.len() as int - 1]
    }
}

// ghost predicate NoLoss(price: int, a: seq<int>)
spec fn no_loss(price: int, a: Seq<int>) -> bool
    recommends a.len() > 0,
{
    price * a.len() >= sum_spec(a)
}

// ghost predicate IsMinimalEqualPrice(price: int, a: seq<int>)
spec fn is_minimal_equal_price(price: int, a: Seq<int>) -> bool
    recommends a.len() > 0,
{
    no_loss(price, a) && !no_loss(price - 1, a)
}

// Lemma: sum_spec(a.push(x)) == sum_spec(a) + x
proof fn lemma_sum_append(a: Seq<int>, x: int)
    ensures
        sum_spec(a.push(x)) == sum_spec(a) + x,
{
    let ax = a.push(x);
    assert(ax.take(ax.len() as int - 1) =~= a);
}

// Lemma: bound on sum_spec
proof fn lemma_sum_bound(a: Seq<int>, lo: int, hi: int)
    requires
        forall|i: int| 0 <= i < a.len() ==> lo <= (#[trigger] a[i]) <= hi,
    ensures
        lo * a.len() <= sum_spec(a) <= hi * a.len(),
    decreases a.len(),
{
    if a.len() == 0 {
    } else {
        let prefix = a.take(a.len() as int - 1);
        assert forall|i: int| 0 <= i < prefix.len() implies lo <= (#[trigger] prefix[i]) <= hi by {
            assert(prefix[i] == a[i]);
        }
        lemma_sum_bound(prefix, lo, hi);
        assert(lo * a.len() == lo * (a.len() - 1) + lo) by (nonlinear_arith)
            requires a.len() > 0;
        assert(hi * a.len() == hi * (a.len() - 1) + hi) by (nonlinear_arith)
            requires a.len() > 0;
    }
}

// Lemma: ceiling division gives minimal equal price
// ceil(s, n) = if s % n == 0 then s/n else s/n + 1  (Euclidean div/mod)
proof fn lemma_ceil_div_is_minimal(s: int, n: int)
    requires n > 0,
    ensures
        ({
            let r = s % n;
            let q = s / n;
            let price = if r == 0 { q } else { q + 1 };
            &&& price * n >= s
            &&& (price - 1) * n < s
        }),
{
    let q = s / n;
    let r = s % n;
    lemma_fundamental_div_mod(s, n);
    // gives: n * q + r == s
    lemma_mod_bound(s, n);
    // gives: 0 <= r < n

    if r == 0 {
        assert(n * q == s);
        assert(q * n == s) by (nonlinear_arith)
            requires n * q == s;
        assert((q - 1) * n == s - n) by (nonlinear_arith)
            requires q * n == s;
    } else {
        assert(n * q == s - r);
        assert(q * n == s - r) by (nonlinear_arith)
            requires n * q == s - r;
        assert((q + 1) * n == s - r + n) by (nonlinear_arith)
            requires q * n == s - r;
        assert((q + 1) * n >= s);
        assert(q * n < s);
    }
}

// Lemma: for non-negative a and positive b, (a + b - 1) / b == ceil(a/b) in Euclidean
proof fn lemma_ceil_formula_nonneg(a: int, b: int)
    requires
        a >= 0,
        b > 0,
    ensures
        (a + b - 1) / b == (if a % b == 0 { a / b } else { a / b + 1 }),
{
    let q = a / b;
    let r = a % b;
    lemma_fundamental_div_mod(a, b);
    lemma_mod_bound(a, b);
    // b * q + r == a, 0 <= r < b

    if r == 0 {
        // a + b - 1 = b*q + b - 1
        // (a + b - 1) / b: we need b*q + (b-1) with 0 <= b-1 < b, so quotient = q
        assert(a + b - 1 == b * q + (b - 1)) by (nonlinear_arith)
            requires b * q + r == a, r == 0;
        assert((a + b - 1) / b == q) by (nonlinear_arith)
            requires
                a + b - 1 == b * q + (b - 1),
                b > 0,
                0 <= b - 1,
                b - 1 < b;
    } else {
        // a + b - 1 = b*q + r + b - 1 = b*(q+1) + (r - 1)
        // 0 <= r - 1 < b - 1 < b, so quotient = q + 1
        assert(a + b - 1 == b * (q + 1) + (r - 1)) by (nonlinear_arith)
            requires b * q + r == a;
        assert((a + b - 1) / b == q + 1) by (nonlinear_arith)
            requires
                a + b - 1 == b * (q + 1) + (r - 1),
                b > 0,
                0 <= r - 1,
                r - 1 < b;
    }
}

// Lemma: ceil(s/n) = -floor(-s/n) for s < 0, n > 0
proof fn lemma_ceil_neg(s: int, n: int)
    requires
        s < 0,
        n > 0,
    ensures
        (if s % n == 0 { s / n } else { s / n + 1 }) == -((-s) / n),
{
    let neg_s = -s;  // neg_s > 0
    lemma_fundamental_div_mod(s, n);
    lemma_mod_bound(s, n);
    let q = s / n;
    let r = s % n;
    // n * q + r == s, 0 <= r < n

    lemma_fundamental_div_mod(neg_s, n);
    lemma_mod_bound(neg_s, n);
    let q_pos = neg_s / n;
    let r_pos = neg_s % n;
    // n * q_pos + r_pos == neg_s == -s, 0 <= r_pos < n

    // From n * q + r == s and n * q_pos + r_pos == -s:
    // n * (q + q_pos) + (r + r_pos) == 0
    // So n * (q + q_pos) == -(r + r_pos)

    if r == 0 {
        // s = n * q, neg_s = -n * q = n * (-q)
        // q_pos = -q, r_pos = 0
        // ceil(s/n) = q
        // -floor(-s/n) = -(q_pos) = -(-q) = q
        assert(n * (q + q_pos) == -(r + r_pos)) by (nonlinear_arith)
            requires n * q + r == s, n * q_pos + r_pos == -s;
        assert(r + r_pos >= 0);
        assert(-(r + r_pos) <= 0);
        // n * (q + q_pos) <= 0, and n > 0, so q + q_pos <= 0
        // Also r + r_pos < 2*n, so -(r + r_pos) > -2*n
        // n * (q + q_pos) > -2*n, so q + q_pos > -2
        // Combined: -1 <= q + q_pos <= 0
        // Since r = 0: n*(q+q_pos) = -r_pos, and 0 <= r_pos < n
        // n*(q+q_pos) = -r_pos, so -n < n*(q+q_pos) <= 0
        // Since n > 0: -1 < q+q_pos <= 0, so q+q_pos = 0
        assert(q + q_pos == 0) by (nonlinear_arith)
            requires n * (q + q_pos) + (r + r_pos) == 0, r == 0, 0 <= r_pos, r_pos < n, n > 0;
        assert(q == -q_pos);
        // ceil = q = -q_pos = -(neg_s / n)
    } else {
        // r > 0
        // ceil(s/n) = q + 1
        // We need: q + 1 == -q_pos
        assert(n * (q + q_pos) + (r + r_pos) == 0) by (nonlinear_arith)
            requires n * q + r == s, n * q_pos + r_pos == -s;
        // 0 < r < n and 0 <= r_pos < n, so 0 < r + r_pos < 2*n
        // n * (q + q_pos) = -(r + r_pos), so -2*n < n*(q+q_pos) < 0
        // Since n > 0: -2 < q + q_pos < 0, so q + q_pos == -1
        assert(q + q_pos == -1) by (nonlinear_arith)
            requires
                n * (q + q_pos) + (r + r_pos) == 0,
                0 < r, r < n,
                0 <= r_pos, r_pos < n,
                n > 0;
        assert(q + 1 == -q_pos);
        // ceil = q + 1 = -q_pos = -(neg_s / n)
    }
}

// Main method
fn equalize_price(a: &Vec<i64>) -> (price: i64)
    requires
        a@.len() > 0,
        a@.len() < 1_000_000,
        forall|i: int| 0 <= i < a@.len() ==> -1_000_000_000 <= (#[trigger] a@[i]) <= 1_000_000_000,
    ensures
        is_minimal_equal_price(price as int, a@.map_values(|v: i64| v as int)),
{
    let ghost a_spec: Seq<int> = a@.map_values(|v: i64| v as int);
    let n: usize = a.len();
    let mut s: i64 = 0;
    let mut i: usize = 0;

    proof {
        assert(a_spec.len() == n as int);
        assert(sum_spec(a_spec.take(0)) == 0int) by {
            assert(a_spec.take(0).len() == 0);
        }
    }

    // Loop: compute s = sum_spec(a_spec)
    while i < n
        invariant
            0 <= i <= n,
            n == a@.len(),
            n > 0,
            n < 1_000_000,
            a_spec =~= a@.map_values(|v: i64| v as int),
            a_spec.len() == n,
            s as int == sum_spec(a_spec.take(i as int)),
            forall|j: int| 0 <= j < a@.len() ==> -1_000_000_000 <= (#[trigger] a@[j]) <= 1_000_000_000,
            forall|j: int| 0 <= j < a_spec.len() ==> -1_000_000_000 <= (#[trigger] a_spec[j]) <= 1_000_000_000,
            -(i as int) * 1_000_000_000 <= s <= (i as int) * 1_000_000_000,
        decreases n - i,
    {
        proof {
            assert(a_spec.take((i + 1) as int) =~= a_spec.take(i as int).push(a_spec[i as int]));
            lemma_sum_append(a_spec.take(i as int), a_spec[i as int]);
            assert(a_spec[i as int] == a@[i as int] as int);
            assert((i as int + 1) * 1_000_000_000 == (i as int) * 1_000_000_000 + 1_000_000_000) by (nonlinear_arith)
                requires i as int >= 0;
            assert(-((i as int + 1) * 1_000_000_000) == -((i as int) * 1_000_000_000) - 1_000_000_000) by (nonlinear_arith)
                requires i as int >= 0;
        }
        s = s + a[i as usize] as i64;
        i = i + 1;
    }

    proof {
        assert(a_spec.take(n as int) =~= a_spec);
    }
    // Now s as int == sum_spec(a_spec)

    let n_i64 = n as i64;

    // Compute price = ceil(s / n)
    // For s >= 0: use (s + n - 1) / n (non-negative operands)
    // For s < 0: use -((-s) / n) (non-negative operands for the inner division)

    let price: i64;

    if s >= 0 {
        let s_adj: i64 = s + n_i64 - 1;
        // s_adj >= 0 since s >= 0 and n >= 1
        price = s_adj / n_i64;

        proof {
            let sv = s as int;
            let nv = n as int;

            // For non-negative i64 operands, Rust / == Euclidean /
            // s_adj as int == sv + nv - 1 >= 0
            assert(price as int == (s_adj as int) / (n_i64 as int));
            assert(s_adj as int == sv + nv - 1);

            // (sv + nv - 1) / nv == ceil(sv / nv)
            lemma_ceil_formula_nonneg(sv, nv);

            // ceil(sv / nv) is the minimal price
            lemma_ceil_div_is_minimal(sv, nv);

            // Connect
            let ceil_price = if sv % nv == 0 { sv / nv } else { sv / nv + 1 };
            assert(price as int == ceil_price);
            assert(ceil_price * nv >= sv);
            assert((ceil_price - 1) * nv < sv);
            assert(sv == sum_spec(a_spec));
            assert(nv == a_spec.len() as int);
            assert(no_loss(price as int, a_spec));
            assert(!no_loss(price as int - 1, a_spec));
        }
    } else {
        // s < 0
        let neg_s: i64 = -s;  // neg_s > 0 (no overflow since s > -10^15 and i64::MAX > 10^15)
        let floor_neg: i64 = neg_s / n_i64;  // non-negative operands
        price = -floor_neg;

        proof {
            let sv = s as int;
            let nv = n as int;

            // neg_s as int == -sv > 0
            // floor_neg as int == (-sv) / nv  (non-negative Euclidean)
            assert(floor_neg as int == (neg_s as int) / (n_i64 as int));
            assert(neg_s as int == -sv);

            // price as int == -floor_neg as int == -((-sv) / nv)
            assert(price as int == -((-sv) / nv));

            // By lemma_ceil_neg: ceil(sv/nv) == -((-sv)/nv)
            lemma_ceil_neg(sv, nv);
            let ceil_price = if sv % nv == 0 { sv / nv } else { sv / nv + 1 };
            assert(ceil_price == -((-sv) / nv));
            assert(price as int == ceil_price);

            // ceil_price is minimal
            lemma_ceil_div_is_minimal(sv, nv);
            assert(ceil_price * nv >= sv);
            assert((ceil_price - 1) * nv < sv);
            assert(sv == sum_spec(a_spec));
            assert(nv == a_spec.len() as int);
            assert(no_loss(price as int, a_spec));
            assert(!no_loss(price as int - 1, a_spec));
        }
    }

    price
}

fn main() {}

} // verus!

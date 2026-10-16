use vstd::prelude::*;

verus! {

// Count occurrences of value v in a sequence
pub open spec fn count_int(s: Seq<int>, v: int) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[s.len() - 1] == v { 1 as nat } else { 0 as nat }) + count_int(s.subrange(0, s.len() - 1), v)
    }
}

// Given letter inventory counts, can we spell `ones` copies of "one" and `zeros` copies of "zero"?
pub open spec fn feasible_counts(cn: nat, cz: nat, cr: nat, co: nat, ce: nat,
                                  ones: nat, zeros: nat) -> bool
{
    ones <= cn &&
    zeros <= cz &&
    zeros <= cr &&
    ones + zeros <= co &&
    ones + zeros <= ce
}

// Is the binary number [1]^x1 ++ [0]^y1  >=  [1]^x2 ++ [0]^y2 ?
pub open spec fn binary_geq(x1: nat, y1: nat, x2: nat, y2: nat) -> bool
{
    if x2 == 0 {
        true
    } else if x1 == 0 {
        false
    } else {
        x1 + y1 > x2 + y2 || (x1 + y1 == x2 + y2 && x1 >= x2)
    }
}

// Count occurrences of character c in char sequence s
pub open spec fn count_char(s: Seq<char>, c: char) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[s.len() - 1] == c { 1 as nat } else { 0 as nat }) + count_char(s.subrange(0, s.len() - 1), c)
    }
}

// Helper: CountChar of s[..i+1] in terms of s[..i]
proof fn count_char_step(s: Seq<char>, i: nat, c: char)
    requires
        0 <= i < s.len(),
    ensures
        count_char(s.subrange(0, (i + 1) as int), c) ==
            count_char(s.subrange(0, i as int), c) + (if s[i as int] == c { 1 as nat } else { 0 as nat }),
{
    assert(s.subrange(0, (i + 1) as int).subrange(0, i as int) =~= s.subrange(0, i as int));
}

// CountInt of a sequence of all 1s
proof fn count_int_ones_seq(n: nat)
    ensures
        count_int(Seq::new(n as nat, |i: int| 1int), 1) == n,
        count_int(Seq::new(n as nat, |i: int| 1int), 0) == 0,
    decreases n,
{
    if n > 0 {
        assert(Seq::new(n as nat, |i: int| 1int).subrange(0, (n - 1) as int) =~= Seq::new((n - 1) as nat, |i: int| 1int));
        count_int_ones_seq((n - 1) as nat);
    }
}

// CountInt of a sequence of all 0s
proof fn count_int_zeros_seq(n: nat)
    ensures
        count_int(Seq::new(n as nat, |i: int| 0int), 0) == n,
        count_int(Seq::new(n as nat, |i: int| 0int), 1) == 0,
    decreases n,
{
    if n > 0 {
        assert(Seq::new(n as nat, |i: int| 0int).subrange(0, (n - 1) as int) =~= Seq::new((n - 1) as nat, |i: int| 0int));
        count_int_zeros_seq((n - 1) as nat);
    }
}

// CountInt distributes over concatenation
proof fn count_int_concat(a: Seq<int>, b: Seq<int>, v: int)
    ensures
        count_int(a + b, v) == count_int(a, v) + count_int(b, v),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        assert((a + b).subrange(0, (a + b).len() - 1) =~= a + b.subrange(0, b.len() - 1));
        count_int_concat(a, b.subrange(0, b.len() - 1), v);
    }
}

// Optimality: the greedy choice is optimal
proof fn optimality_lemma(cn: nat, cz: nat, cr: nat, co: nat, ce: nat,
                           x: nat, y: nat, xp: nat, yp: nat)
    requires
        x <= co && x <= cn && x <= ce,
        x == co || x == cn || x == ce,
        y <= cz && y <= ce - x && y <= cr && y <= co - x,
        y == cz || y == ce - x || y == cr || y == co - x,
        feasible_counts(cn, cz, cr, co, ce, xp, yp),
    ensures
        binary_geq(x, y, xp, yp),
{
    // From feasibility: xp <= cn, xp <= co, xp <= ce
    assert(xp <= cn);
    assert(xp <= co);
    assert(xp <= ce);
    // So xp <= x = min(cn, co, ce)
    assert(xp <= x);

    if xp == 0 {
        // BinaryGeq(x, y, 0, yp) is true by definition
    } else {
        // Both x > 0, xp > 0
        if y == co - x {
            assert(x + y == co);
            assert(xp + yp <= co);
        } else if y == ce - x {
            assert(x + y == ce);
            assert(xp + yp <= ce);
        } else if y == cz {
            assert(yp <= cz);
            assert(yp <= y);
            assert(xp + yp <= x + y);
        } else {
            assert(y == cr);
            assert(yp <= cr);
            assert(yp <= y);
            assert(xp + yp <= x + y);
        }
    }
}

fn cards(s: &Vec<char>) -> (result: Vec<i64>)
    requires
        forall|i: int| #![auto] 0 <= i < s.len() ==> (s[i] == 'z' || s[i] == 'e' || s[i] == 'r' || s[i] == 'o' || s[i] == 'n'),
    ensures
        ({
            let result_seq = result@.map(|_idx: int, x: i64| x as int);
            let ones = count_int(result_seq, 1);
            let zeros = count_int(result_seq, 0);
            let cn = count_char(s@, 'n');
            let cz = count_char(s@, 'z');
            let cr = count_char(s@, 'r');
            let co = count_char(s@, 'o');
            let ce = count_char(s@, 'e');
            result.len() == ones + zeros &&
            result_seq =~= Seq::new(ones as nat, |i: int| 1int) + Seq::new(zeros as nat, |i: int| 0int) &&
            feasible_counts(cn, cz, cr, co, ce, ones, zeros) &&
            forall|a: nat, b: nat| feasible_counts(cn, cz, cr, co, ce, a, b) ==> binary_geq(ones, zeros, a, b)
        }),
{
    let mut z: u64 = 0;
    let mut e: u64 = 0;
    let mut r: u64 = 0;
    let mut o: u64 = 0;
    let mut n: u64 = 0;

    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            z as nat == count_char(s@.subrange(0, i as int), 'z'),
            e as nat == count_char(s@.subrange(0, i as int), 'e'),
            r as nat == count_char(s@.subrange(0, i as int), 'r'),
            o as nat == count_char(s@.subrange(0, i as int), 'o'),
            n as nat == count_char(s@.subrange(0, i as int), 'n'),
            z <= i as u64,
            e <= i as u64,
            r <= i as u64,
            o <= i as u64,
            n <= i as u64,
            forall|j: int| #![auto] 0 <= j < s.len() ==> (s[j] == 'z' || s[j] == 'e' || s[j] == 'r' || s[j] == 'o' || s[j] == 'n'),
        decreases s.len() - i,
    {
        proof {
            count_char_step(s@, i as nat, 'z');
            count_char_step(s@, i as nat, 'e');
            count_char_step(s@, i as nat, 'r');
            count_char_step(s@, i as nat, 'o');
            count_char_step(s@, i as nat, 'n');
        }
        let c = s[i];
        if c == 'z' {
            z = z + 1;
        } else if c == 'e' {
            e = e + 1;
        } else if c == 'r' {
            r = r + 1;
        } else if c == 'o' {
            o = o + 1;
        } else {
            assert(s@[i as int] == 'n');
            n = n + 1;
        }
        i = i + 1;
    }

    proof {
        assert(s@.subrange(0, s@.len() as int) =~= s@);
    }

    // Save original character counts as ghost
    let ghost gcn = n as nat;
    let ghost gcz = z as nat;
    let ghost gcr = r as nat;
    let ghost gco = o as nat;
    let ghost gce = e as nat;

    // Compute x = min(o, n, e)
    let mut x: u64 = o;
    if n < x { x = n; }
    if e < x { x = e; }

    assert(x as nat <= gco && x as nat <= gcn && x as nat <= gce);
    assert(x as nat == gco || x as nat == gcn || x as nat == gce);

    // Subtract letters used by "one"s
    o = o - x;
    n = n - x;
    e = e - x;

    // Compute y = min(z, e, r, o)
    let mut y: u64 = z;
    if e < y { y = e; }
    if r < y { y = r; }
    if o < y { y = o; }

    assert(y as nat <= gcz && y as nat <= gce - x as nat && y as nat <= gcr && y as nat <= gco - x as nat);
    assert(y as nat == gcz || y as nat == gce - x as nat || y as nat == gcr || y as nat == gco - x as nat);

    // Build result: x ones followed by y zeros
    let mut result: Vec<i64> = Vec::new();
    let mut j: u64 = 0;
    while j < x
        invariant
            0 <= j <= x,
            result.len() == j as nat,
            forall|k: int| 0 <= k < j ==> result@[k] == 1i64,
        decreases x - j,
    {
        result.push(1i64);
        j = j + 1;
    }
    let mut j2: u64 = 0;
    while j2 < y
        invariant
            0 <= j2 <= y,
            result.len() == x as nat + j2 as nat,
            forall|k: int| 0 <= k < x ==> result@[k] == 1i64,
            forall|k: int| x as int <= k < (x + j2) as int ==> result@[k] == 0i64,
        decreases y - j2,
    {
        result.push(0i64);
        j2 = j2 + 1;
    }

    proof {
        // Show result_seq matches the spec
        let result_seq = result@.map(|_idx: int, v: i64| v as int);
        let ones_seq = Seq::new(x as nat, |i: int| 1int);
        let zeros_seq = Seq::new(y as nat, |i: int| 0int);

        // Prove result_seq =~= ones_seq + zeros_seq
        assert(result_seq.len() == (x + y) as nat);
        assert((ones_seq + zeros_seq).len() == (x + y) as nat);
        assert forall|k: int| 0 <= k < result_seq.len() implies result_seq[k] == (ones_seq + zeros_seq)[k] by {
            if k < x as int {
                assert(result@[k] == 1i64);
                assert(result_seq[k] == 1);
                assert((ones_seq + zeros_seq)[k] == ones_seq[k]);
                assert(ones_seq[k] == 1);
            } else {
                assert(result@[k] == 0i64);
                assert(result_seq[k] == 0);
                assert((ones_seq + zeros_seq)[k] == zeros_seq[k - x as int]);
                assert(zeros_seq[k - x as int] == 0);
            }
        }
        assert(result_seq =~= ones_seq + zeros_seq);

        // Establish CountInt values
        count_int_ones_seq(x as nat);
        count_int_zeros_seq(y as nat);
        count_int_concat(ones_seq, zeros_seq, 1);
        count_int_concat(ones_seq, zeros_seq, 0);

        assert(count_int(result_seq, 1) == x as nat);
        assert(count_int(result_seq, 0) == y as nat);

        // Feasibility
        assert(feasible_counts(gcn, gcz, gcr, gco, gce, x as nat, y as nat));

        // Optimality
        assert forall|a: nat, b: nat| feasible_counts(gcn, gcz, gcr, gco, gce, a, b) implies binary_geq(x as nat, y as nat, a, b) by {
            optimality_lemma(gcn, gcz, gcr, gco, gce, x as nat, y as nat, a, b);
        }
    }

    result
}

fn main() {}

} // verus!

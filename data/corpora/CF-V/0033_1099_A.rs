use vstd::prelude::*;

verus! {

spec fn max0(x: int) -> int {
    if x < 0 { 0 } else { x }
}

spec fn weight_after_height(weight: int, height: int,
                            u1: int, d1: int, u2: int, d2: int) -> int
{
    let after_gain = weight + height;
    let after_stone1 = if height == d1 { max0(after_gain - u1) } else { after_gain };
    let after_stone2 = if height == d2 { max0(after_stone1 - u2) } else { after_stone1 };
    after_stone2
}

spec fn heights(h: int) -> Seq<int>
    decreases (if h >= 0 { h + 1 } else { 0 }),
{
    if h < 0 {
        Seq::<int>::empty()
    } else {
        Seq::<int>::empty().push(h).add(heights((h - 1) as int))
    }
}

spec fn roll_through(w: int, hs: Seq<int>,
                     u1: int, d1: int, u2: int, d2: int) -> int
    decreases hs.len(),
{
    if hs.len() == 0 {
        w
    } else {
        roll_through(
            weight_after_height(w, hs[0], u1, d1, u2, d2),
            hs.subrange(1, hs.len() as int),
            u1, d1, u2, d2,
        )
    }
}

proof fn lemma_heights_cons(h: int)
    requires h >= 0,
    ensures heights(h) =~= Seq::<int>::empty().push(h).add(heights((h - 1) as int)),
{
}

proof fn lemma_roll_through_cons(w: int, head: int, tail: Seq<int>,
                                  u1: int, d1: int, u2: int, d2: int)
    ensures roll_through(w, Seq::<int>::empty().push(head).add(tail), u1, d1, u2, d2)
            == roll_through(weight_after_height(w, head, u1, d1, u2, d2), tail, u1, d1, u2, d2),
{
    let s = Seq::<int>::empty().push(head).add(tail);
    assert(s.len() > 0);
    assert(s[0] == head);
    assert(s.subrange(1, s.len() as int) =~= tail);
}

proof fn lemma_weight_after_height_bound(weight: int, height: int,
                                          u1: int, d1: int, u2: int, d2: int)
    requires weight >= 0, height >= 0, u1 >= 0, u2 >= 0,
    ensures
        0 <= weight_after_height(weight, height, u1, d1, u2, d2) <= weight + height,
{
}

/// Triangular number: tri(n) = n*(n+1)/2 for n >= 0, 0 otherwise.
spec fn tri(n: int) -> int {
    if n <= 0 { 0 } else { n * (n + 1) / 2 }
}

/// tri(n) = tri(n-1) + n for n >= 1
proof fn lemma_tri_step(n: int)
    requires n >= 1,
    ensures tri(n) == tri(n - 1) + n,
{
    if n == 1 {
        assert(tri(1) == 1 * 2 / 2);
        assert(tri(0) == 0);
    } else {
        assert(tri(n) == n * (n + 1) / 2);
        assert(n - 1 >= 1);
        assert(tri(n - 1) == (n - 1) * ((n - 1) + 1) / 2);
        assert(tri(n - 1) == (n - 1) * n / 2);
        assert(n * (n + 1) == (n - 1) * n + 2 * n) by(nonlinear_arith);
    }
}

proof fn lemma_tri_bound(h: int)
    requires h >= 0,
    ensures tri(h) <= h * h,
{
    assert(h * (h + 1) / 2 <= h * h) by(nonlinear_arith)
        requires h >= 0;
}

fn snowball(w: i64, h: i64, u1: i64, d1: i64, u2: i64, d2: i64) -> (final_weight: i64)
    requires
        0 <= w,
        0 <= h,
        0 <= u1,
        0 <= u2,
        0 <= d1,
        0 <= d2,
        // Ensure w + tri(h) + h fits in i64.
        // tri(h) <= h*h, so w + h*h + h < i64::MAX suffices.
        w as int + (h as int) * (h as int) + (h as int) < i64::MAX as int,
    ensures final_weight as int == roll_through(w as int, heights(h as int), u1 as int, d1 as int, u2 as int, d2 as int),
{
    let mut final_weight: i64 = w;
    let mut i: i64 = h;

    while i >= 0
        invariant
            -1 <= i <= h,
            0 <= final_weight,
            // The key invariant: weight plus remaining sum fits i64.
            // Specifically: final_weight + tri(i) <= w + tri(h)
            // And: w + tri(h) + h < i64::MAX
            final_weight as int + tri(i as int) <= w as int + tri(h as int),
            w as int + (h as int) * (h as int) + (h as int) < i64::MAX as int,
            0 <= h,
            i <= h,
            0 <= u1,
            0 <= u2,
            0 <= d1,
            0 <= d2,
            roll_through(w as int, heights(h as int), u1 as int, d1 as int, u2 as int, d2 as int)
                == roll_through(final_weight as int, heights(i as int), u1 as int, d1 as int, u2 as int, d2 as int),
        decreases (i + 1) as int,
    {
        let old_weight = final_weight;
        proof {
            // Show final_weight + i doesn't overflow:
            // final_weight <= w + tri(h) - tri(i)
            // final_weight + i <= w + tri(h) - tri(i) + i
            // For i >= 1: tri(i) = tri(i-1) + i, so -tri(i) + i = -tri(i-1).
            // So final_weight + i <= w + tri(h) - tri(i-1) <= w + tri(h)
            // tri(h) <= h*h (by lemma_tri_bound).
            // So final_weight + i <= w + h*h < i64::MAX - h < i64::MAX.
            if i >= 1 {
                lemma_tri_step(i as int);
            }
            lemma_tri_bound(h as int);
        }
        final_weight = final_weight + i;
        if i == d1 {
            if final_weight >= u1 {
                final_weight = final_weight - u1;
            } else {
                final_weight = 0;
            }
        }
        if i == d2 {
            if final_weight >= u2 {
                final_weight = final_weight - u2;
            } else {
                final_weight = 0;
            }
        }
        proof {
            lemma_weight_after_height_bound(old_weight as int, i as int, u1 as int, d1 as int, u2 as int, d2 as int);
            assert(final_weight as int == weight_after_height(old_weight as int, i as int, u1 as int, d1 as int, u2 as int, d2 as int));
            // Maintain: final_weight + tri(i-1) <= w + tri(h)
            // final_weight <= old_weight + i
            // old_weight + tri(i) <= w + tri(h)
            // For i >= 1: tri(i) = tri(i-1) + i.
            // final_weight + tri(i-1) <= (old_weight + i) + tri(i-1) = old_weight + tri(i) <= w + tri(h). QED.
            // For i == 0: tri(0) = 0, tri(-1) = 0.
            // final_weight <= old_weight + 0 = old_weight.
            // old_weight + tri(0) = old_weight <= w + tri(h).
            // final_weight + tri(-1) = final_weight + 0 = final_weight <= old_weight <= w + tri(h). QED.
            if i >= 1 {
                lemma_tri_step(i as int);
            }

            lemma_heights_cons(i as int);
            lemma_roll_through_cons(
                old_weight as int, i as int, heights((i - 1) as int),
                u1 as int, d1 as int, u2 as int, d2 as int,
            );
        }
        i = i - 1;
    }
    final_weight
}

fn main() {}

} // verus!

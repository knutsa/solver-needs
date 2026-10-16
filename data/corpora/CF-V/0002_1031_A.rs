use vstd::prelude::*;

verus! {

spec fn on_border(r: int, c: int, top: int, left: int, rows: int, cols: int) -> bool {
    rows >= 1 && cols >= 1 &&
    top <= r && r < top + rows && left <= c && c < left + cols &&
    (r == top || r == top + rows - 1 || c == left || c == left + cols - 1)
}

spec fn in_ring(r: int, c: int, w: int, h: int, ring: int) -> bool {
    on_border(r, c, 2 * ring, 2 * ring, h - 4 * ring, w - 4 * ring)
}

spec fn is_gilded(r: int, c: int, w: int, h: int, k: int) -> bool {
    exists|i: int| 0 <= i && i < k && in_ring(r, c, w, h, i)
}

spec fn count_gilded_up_to(w: int, h: int, k: int, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 }
    else {
        let r = (n - 1) / w;
        let c = (n - 1) % w;
        count_gilded_up_to(w, h, k, n - 1) + if is_gilded(r, c, w, h, k) { 1 as int } else { 0 as int }
    }
}

spec fn count_gilded(w: int, h: int, k: int) -> int {
    count_gilded_up_to(w, h, k, w * h)
}

proof fn count_gilded_up_to_bounds(w: int, h: int, k: int, n: int)
    requires
        w >= 1,
        h >= 1,
        0 <= n <= w * h,
    ensures
        0 <= count_gilded_up_to(w, h, k, n) <= n,
    decreases n,
{
    if n > 0 {
        count_gilded_up_to_bounds(w, h, k, n - 1);
    }
}

fn check_in_ring(r: i64, c: i64, w: i64, h: i64, ring: i64) -> (result: bool)
    requires
        0 <= ring,
        0 <= r,
        0 <= c,
        0 <= w,
        0 <= h,
        4 * ring <= i64::MAX,
        w + 2 * ring <= i64::MAX / 2,
        h + 2 * ring <= i64::MAX / 2,
    ensures
        result == in_ring(r as int, c as int, w as int, h as int, ring as int),
{
    let top = 2 * ring;
    let rw: i64 = w - 4 * ring;
    let rh: i64 = h - 4 * ring;
    rh >= 1 && rw >= 1 &&
        top <= r && r < top + rh &&
        top <= c && c < top + rw &&
        (r == top || r == top + rh - 1 || c == top || c == top + rw - 1)
}

fn check_is_gilded(r: i64, c: i64, w: i64, h: i64, k: i64) -> (result: bool)
    requires
        k >= 0,
        0 <= r,
        0 <= c,
        0 <= w,
        0 <= h,
        4 * k <= i64::MAX,
        w + 2 * k <= i64::MAX / 2,
        h + 2 * k <= i64::MAX / 2,
    ensures
        result == is_gilded(r as int, c as int, w as int, h as int, k as int),
{
    let mut result = false;
    let mut j: i64 = 0;
    while j < k
        invariant
            0 <= j <= k,
            0 <= r,
            0 <= c,
            0 <= w,
            0 <= h,
            4 * k <= i64::MAX,
            w + 2 * k <= i64::MAX / 2,
            h + 2 * k <= i64::MAX / 2,
            result <==> exists|i: int| 0 <= i && i < j as int && in_ring(r as int, c as int, w as int, h as int, i),
        decreases k - j,
    {
        let in_r = check_in_ring(r, c, w, h, j);
        if in_r {
            result = true;
        }
        j = j + 1;
    }
    result
}

fn golden_plate(w: i64, h: i64, k: i64) -> (gilded: i64)
    requires
        w >= 1,
        h >= 1,
        k >= 0,
        4 * k <= i64::MAX,
        w + 2 * k <= i64::MAX / 2,
        h + 2 * k <= i64::MAX / 2,
        w * h <= i64::MAX / 2,
    ensures
        gilded as int == count_gilded(w as int, h as int, k as int),
{
    let mut gilded: i64 = 0;
    let mut n: i64 = 0;

    proof {
        count_gilded_up_to_bounds(w as int, h as int, k as int, 0);
    }

    while n < w * h
        invariant
            0 <= n <= w * h,
            w >= 1,
            h >= 1,
            k >= 0,
            4 * k <= i64::MAX,
            w + 2 * k <= i64::MAX / 2,
            h + 2 * k <= i64::MAX / 2,
            w * h <= i64::MAX / 2,
            gilded as int == count_gilded_up_to(w as int, h as int, k as int, n as int),
            0 <= gilded <= n,
        decreases w * h - n,
    {
        let r = n / w;
        let c = n % w;
        let is_g = check_is_gilded(r, c, w, h, k);
        if is_g {
            gilded = gilded + 1;
        }
        n = n + 1;

        proof {
            count_gilded_up_to_bounds(w as int, h as int, k as int, n as int);
        }
    }
    gilded
}

} // verus!

fn main() {}

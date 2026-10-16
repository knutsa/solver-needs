use vstd::prelude::*;

verus! {

spec fn max_of(a: int, b: int) -> int {
    if a > b { a } else { b }
}

spec fn min_of(a: int, b: int) -> int {
    if a < b { a } else { b }
}

spec fn is_valid_solution(x: int, y: int, z: int, a: int, b: int, c: int) -> bool {
    a > 0 && b > 0 && c > 0 &&
    max_of(a, b) == x && max_of(a, c) == y && max_of(b, c) == z
}

spec fn solution_exists(x: int, y: int, z: int) -> bool {
    exists|a: int, b: int, c: int| is_valid_solution(x, y, z, a, b, c)
}

proof fn no_solution_when_cnt_less_than_2(x: int, y: int, z: int, m: int, cnt: int)
    requires
        x > 0 && y > 0 && z > 0,
        m == max_of(x, max_of(y, z)),
        cnt == (if x == m { 1int } else { 0 }) + (if y == m { 1int } else { 0 }) + (if z == m { 1int } else { 0 }),
        cnt < 2,
    ensures
        !solution_exists(x, y, z),
{
    // We prove by contradiction: for any a', b', c', IsValidSolution is false.
    // The key insight: the largest of a', b', c' appears in at least 2 pairwise maxima,
    // so max(x,y,z) must appear at least twice among x,y,z. But cnt < 2 means it doesn't.
    assert forall|a2: int, b2: int, c2: int| !is_valid_solution(x, y, z, a2, b2, c2) by {
        if a2 > 0 && b2 > 0 && c2 > 0 && max_of(a2, b2) == x && max_of(a2, c2) == y && max_of(b2, c2) == z {
            if a2 >= b2 && a2 >= c2 {
                // a2 is largest: max(a2,b2) = a2 = x, max(a2,c2) = a2 = y => x == y
                assert(max_of(a2, b2) == a2);
                assert(max_of(a2, c2) == a2);
                assert(x == a2 && y == a2);
                // z = max(b2,c2) <= a2 = x, so m = max(x,y,z) = x = y
                // Both x==m and y==m => cnt >= 2, contradiction
                assert(x == y);
                assert(max_of(b2, c2) <= a2);
                assert(z <= x);
                assert(m == x);
            } else if b2 >= a2 && b2 >= c2 {
                // b2 is largest: max(a2,b2) = b2 = x, max(b2,c2) = b2 = z => x == z
                assert(max_of(a2, b2) == b2);
                assert(max_of(b2, c2) == b2);
                assert(x == b2 && z == b2);
                assert(x == z);
                assert(max_of(a2, c2) <= b2);
                assert(y <= x);
                assert(m == x);
            } else {
                // c2 is largest: max(a2,c2) = c2 = y, max(b2,c2) = c2 = z => y == z
                assert(c2 >= a2 && c2 >= b2);
                assert(max_of(a2, c2) == c2);
                assert(max_of(b2, c2) == c2);
                assert(y == c2 && z == c2);
                assert(y == z);
                assert(max_of(a2, b2) <= c2);
                assert(x <= y);
                assert(m == y);
            }
        }
    };
}

fn three_pairwise_maximums(x: i64, y: i64, z: i64) -> (result: (bool, i64, i64, i64))
    requires
        x > 0 && y > 0 && z > 0,
    ensures
        result.0 == solution_exists(x as int, y as int, z as int),
        result.0 ==> is_valid_solution(x as int, y as int, z as int, result.1 as int, result.2 as int, result.3 as int),
{
    let mut m = x;
    if y > m { m = y; }
    if z > m { m = z; }

    let mut cnt: i64 = 0;
    if x == m { cnt = cnt + 1; }
    if y == m { cnt = cnt + 1; }
    if z == m { cnt = cnt + 1; }

    if cnt >= 2 {
        let possible = true;
        let a = if x <= y { x } else { y };
        let b = if x <= z { x } else { z };
        let c = if y <= z { y } else { z };

        proof {
            // Show the witness satisfies the predicate
            assert(is_valid_solution(x as int, y as int, z as int, a as int, b as int, c as int));
            // Provide the existential witness
        }

        (possible, a, b, c)
    } else {
        let possible = false;
        let a: i64 = 0;
        let b: i64 = 0;
        let c: i64 = 0;

        proof {
            let ghost_m = max_of(x as int, max_of(y as int, z as int));
            let ghost_cnt = (if x as int == ghost_m { 1int } else { 0 }) + (if y as int == ghost_m { 1int } else { 0 }) + (if z as int == ghost_m { 1int } else { 0 });
            // Show ghost_m matches m and ghost_cnt matches cnt
            assert(ghost_m == m as int);
            assert(ghost_cnt == cnt as int);
            assert(ghost_cnt < 2);
            no_solution_when_cnt_less_than_2(x as int, y as int, z as int, ghost_m, ghost_cnt);
        }

        (possible, a, b, c)
    }
}

fn main() {}

} // verus!

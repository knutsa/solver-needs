use vstd::prelude::*;

verus! {

spec fn beautiful(ny: int, nb: int, nr: int) -> bool {
    nb == ny + 1 && nr == nb + 1
}

spec fn valid_choice(y: int, b: int, r: int, ny: int, nb: int, nr: int) -> bool {
    0 <= ny <= y && 0 <= nb <= b && 0 <= nr <= r && beautiful(ny, nb, nr)
}

fn max_ornaments(y: i64, b: i64, r: i64) -> (total: i64)
    requires
        y >= 1,
        b >= 2,
        r >= 3,
        y <= 3_074_457_345_618_258_601i64,
    ensures
        exists|ny: int| #[trigger] valid_choice(y as int, b as int, r as int, ny, ny + 1, ny + 2) &&
            0 <= ny <= y as int &&
            total as int == ny + (ny + 1) + (ny + 2),
        forall|ny: int| 0 <= ny <= y as int ==>
            #[trigger] valid_choice(y as int, b as int, r as int, ny, ny + 1, ny + 2) ==>
            ny + (ny + 1) + (ny + 2) <= total as int,
{
    let mut m = y;
    if b - 1 < m { m = b - 1; }
    if r - 2 < m { m = r - 2; }
    let total = 3 * m + 3;

    proof {
        // Prove the existential: m is a valid choice
        assert(valid_choice(y as int, b as int, r as int, m as int, m as int + 1, m as int + 2));

        // Prove optimality: for any valid ny, ny <= m so 3*ny+3 <= 3*m+3 = total
        assert forall|ny: int| 0 <= ny <= y as int ==>
            #[trigger] valid_choice(y as int, b as int, r as int, ny, ny + 1, ny + 2) ==>
            ny + (ny + 1) + (ny + 2) <= total as int by {
            if 0 <= ny <= y as int && valid_choice(y as int, b as int, r as int, ny, ny + 1, ny + 2) {
                assert(ny + 1 <= b as int);
                assert(ny + 2 <= r as int);
                assert(ny <= m as int);
            }
        };
    }

    total
}

fn main() {}

} // verus!
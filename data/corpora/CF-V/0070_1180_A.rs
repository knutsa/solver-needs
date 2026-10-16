use vstd::prelude::*;

verus! {

// ghost function Abs
pub open spec fn abs_val(x: int) -> int {
    if x >= 0 { x } else { -x }
}

// ghost predicate InRhombus
pub open spec fn in_rhombus(x: int, y: int, n: int) -> bool
    recommends n >= 1
{
    abs_val(x) + abs_val(y) <= n - 1
}

// ghost function RowWidth
pub open spec fn row_width(x: int, r: int) -> int
    recommends r >= 0
{
    if abs_val(x) > r { 0 }
    else { 2 * (r - abs_val(x)) + 1 }
}

// ghost function SumRows
pub open spec fn sum_rows(lo: int, hi: int, r: int) -> int
    recommends r >= 0
    decreases (if lo <= hi { hi - lo + 1 } else { 0 }) as int
{
    if lo > hi { 0 }
    else { row_width(lo, r) + sum_rows(lo + 1, hi, r) }
}

// ghost function RhombusCellCount
pub open spec fn rhombus_cell_count(n: int) -> int
    recommends n >= 1
{
    sum_rows(-(n - 1), n - 1, n - 1)
}

// lemma SumRowsAppend
proof fn sum_rows_append(lo: int, hi: int, r: int)
    requires
        r >= 0,
        lo <= hi,
    ensures
        sum_rows(lo, hi, r) == sum_rows(lo, hi - 1, r) + row_width(hi, r),
    decreases hi - lo,
{
    reveal_with_fuel(sum_rows, 12);
    if lo == hi {
    } else {
        sum_rows_append(lo + 1, hi, r);
    }
}

// lemma SumRowsRadiusStep
proof fn sum_rows_radius_step(lo: int, hi: int, r: int)
    requires
        r >= 1,
        -(r - 1) <= lo,
        lo <= hi,
        hi <= r - 1,
    ensures
        sum_rows(lo, hi, r) == sum_rows(lo, hi, r - 1) + 2 * (hi - lo + 1),
    decreases hi - lo,
{
    reveal_with_fuel(sum_rows, 12);
    if lo == hi {
        assert(abs_val(lo) <= r - 1);
    } else {
        sum_rows_radius_step(lo + 1, hi, r);
        assert(abs_val(lo) <= r - 1);
    }
}

// Helper lemma for the algebraic identity
proof fn closed_form_algebra(r: int)
    requires r >= 1,
    ensures
        2 * (r - 1) * (r - 1) + 2 * (r - 1) + 1 + 4 * r
            == 2 * r * r + 2 * r + 1,
{
    assert(2 * (r - 1) * (r - 1) + 2 * (r - 1) + 1 + 4 * r
        == 2 * (r * r - 2 * r + 1) + 2 * r - 2 + 1 + 4 * r) by(nonlinear_arith);
    assert(2 * (r * r - 2 * r + 1) + 2 * r - 2 + 1 + 4 * r
        == 2 * r * r + 2 * r + 1) by(nonlinear_arith);
}

// lemma RhombusCellCountClosedForm
proof fn rhombus_cell_count_closed_form(n: int)
    requires n >= 1,
    ensures rhombus_cell_count(n) == 2 * (n - 1) * (n - 1) + 2 * (n - 1) + 1,
    decreases n,
{
    reveal_with_fuel(sum_rows, 12);
    let r = n - 1;
    if r == 0 {
        // rhombus_cell_count(1) = sum_rows(0, 0, 0) = row_width(0, 0) + 0 = 1
    } else {
        rhombus_cell_count_closed_form(n - 1);
        // IH: rhombus_cell_count(n-1) == 2*(r-1)^2 + 2*(r-1) + 1

        assert(abs_val(-r) == r);
        assert(row_width(-r, r) == 1);
        assert(abs_val(r) == r);
        assert(row_width(r, r) == 1);

        // sum_rows(-r, r, r) = row_width(-r, r) + sum_rows(-(r-1), r, r)
        assert(sum_rows(-r, r, r) == row_width(-r, r) + sum_rows(-(r - 1), r, r));

        // Peel off the last row
        sum_rows_append(-(r - 1), r, r);
        // sum_rows(-(r-1), r, r) == sum_rows(-(r-1), r-1, r) + row_width(r, r)

        // Radius step
        sum_rows_radius_step(-(r - 1), r - 1, r);
        // sum_rows(-(r-1), r-1, r) == sum_rows(-(r-1), r-1, r-1) + 2*(2r-1)

        // Chain together:
        // rhombus_cell_count(n)
        //   = sum_rows(-r, r, r)
        //   = 1 + sum_rows(-(r-1), r, r)
        //   = 1 + sum_rows(-(r-1), r-1, r) + 1
        //   = 1 + sum_rows(-(r-1), r-1, r-1) + 2*(2r-1) + 1
        //   = rhombus_cell_count(n-1) + 4*r
        //   = 2*(r-1)^2 + 2*(r-1) + 1 + 4*r

        closed_form_algebra(r);
    }
}

// method Rhombus
fn rhombus(n: i64) -> (cells: i64)
    requires
        n >= 1,
        // upper bound to prevent overflow: 2*(n-1)^2 + 2*(n-1) + 1 <= i64::MAX
        2 * ((n - 1) as int) * ((n - 1) as int) + 2 * ((n - 1) as int) + 1 <= i64::MAX as int,
    ensures cells == rhombus_cell_count(n as int),
{
    let mut cells: i64 = 1;
    let mut i: i64 = 1;
    while i < n
        invariant
            1 <= i <= n,
            cells as int == 2 * ((i - 1) as int) * ((i - 1) as int) + 2 * ((i - 1) as int) + 1,
            2 * ((n - 1) as int) * ((n - 1) as int) + 2 * ((n - 1) as int) + 1 <= i64::MAX as int,
        decreases n - i,
    {
        // Prove no overflow: cells + i*4 <= 2*(n-1)^2 + 2*(n-1) + 1
        // cells = 2*(i-1)^2 + 2*(i-1) + 1, and cells + 4*i = 2*i^2 + 2*i + 1
        // Since i < n, we have i <= n-1, so 2*i^2 + 2*i + 1 <= 2*(n-1)^2 + 2*(n-1) + 1
        proof {
            let gi = i as int;
            let gn = n as int;
            assert(2 * (gi - 1) * (gi - 1) + 2 * (gi - 1) + 1 + 4 * gi
                == 2 * gi * gi + 2 * gi + 1) by(nonlinear_arith);
            // gi <= gn - 1, so gi^2 <= (gn-1)^2
            assert(gi <= gn - 1);
            assert(gi * gi <= (gn - 1) * (gn - 1)) by(nonlinear_arith)
                requires gi >= 0, gi <= gn - 1;
            assert(2 * gi * gi + 2 * gi + 1
                <= 2 * (gn - 1) * (gn - 1) + 2 * (gn - 1) + 1) by(nonlinear_arith)
                requires gi <= gn - 1, gi * gi <= (gn - 1) * (gn - 1);
        }
        cells = cells + i * 4;
        i = i + 1;
    }
    proof {
        rhombus_cell_count_closed_form(n as int);
    }
    cells
}

} // verus!

fn main() {}

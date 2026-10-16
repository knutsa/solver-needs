use vstd::prelude::*;

verus! {

spec fn can_form_triangle(x: int, y: int, z: int) -> bool {
    x + y > z && x + z > y && y + z > x
}

spec fn sorted(a: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i && i <= j && j < a.len() ==> a[i] <= a[j]
}

spec fn seq_to_int(a: Seq<i64>) -> Seq<int> {
    a.map_values(|x: i64| x as int)
}

proof fn all_triangles_valid(a: Seq<int>)
    requires
        a.len() >= 3,
        sorted(a),
        a[0] + a[1] > a[a.len() - 1],
    ensures
        forall|i: int, j: int, k: int|
            0 <= i && i < j && j < k && k < a.len()
            ==> can_form_triangle(a[i], a[j], a[k]),
{
    let n = a.len();
    assert forall|i: int, j: int, k: int|
        0 <= i && i < j && j < k && k < n
    implies can_form_triangle(a[i], a[j], a[k]) by {
        assert(a[n-1] >= a[1]);
        assert(a[n-1] >= a[0]);
        assert(a[0] > 0);
        assert(a[1] > 0);

        assert(a[i] >= a[0]);
        assert(a[j] >= a[1]);
        assert(a[k] <= a[n - 1]);

        assert(a[i] + a[j] > a[k]);

        assert(a[k] >= a[j]);
        assert(a[i] + a[k] > a[j]);

        assert(a[j] >= a[i]);
        assert(a[j] + a[k] > a[i]);
    }
}

// Bounds for i64 arithmetic safety
spec fn values_bounded(a: Seq<i64>) -> bool {
    forall|i: int| 0 <= i && i < a.len() ==>
        -1_000_000_000 <= a[i] && a[i] <= 1_000_000_000
}

fn bad_triangle(a: &Vec<i64>) -> (ret: ((i64, i64, i64), bool))
    requires
        a@.len() >= 3,
        a@.len() <= 1_000_000_000,
        sorted(seq_to_int(a@)),
        values_bounded(a@),
    ensures
        ret.1 ==> {
            let result = ret.0;
            let sa = seq_to_int(a@);
            &&& 1 <= result.0
            &&& result.0 < result.1
            &&& result.1 < result.2
            &&& result.2 <= a@.len() as i64
            &&& !can_form_triangle(
                sa[result.0 as int - 1],
                sa[result.1 as int - 1],
                sa[result.2 as int - 1],
            )
        },
        !ret.1 ==> forall|i: int, j: int, k: int|
            0 <= i && i < j && j < k && k < a@.len()
            ==> #[trigger] can_form_triangle(
                seq_to_int(a@)[i],
                seq_to_int(a@)[j],
                seq_to_int(a@)[k],
            ),
{
    let ghost sa = seq_to_int(a@);
    let n: i64 = a.len() as i64;

    let x = a[0] + a[1] - a[(n - 1) as usize];
    let y = a[0] - a[1] + a[(n - 1) as usize];
    let z = -a[0] + a[1] + a[(n - 1) as usize];
    if x <= 0 || y <= 0 || z <= 0 {
        return ((1, 2, n), true);
    }

    let x = a[0] + a[(n - 1) as usize] - a[(n - 2) as usize];
    let y = a[0] - a[(n - 1) as usize] + a[(n - 2) as usize];
    let z = -a[0] + a[(n - 1) as usize] + a[(n - 2) as usize];
    if x <= 0 || y <= 0 || z <= 0 {
        return ((1, n - 1, n), true);
    }

    let x = a[0] + a[1] - a[2];
    let y = a[0] - a[1] + a[2];
    let z = -a[0] + a[1] + a[2];
    if x <= 0 || y <= 0 || z <= 0 {
        return ((1, 2, 3), true);
    }

    let x = a[(n - 3) as usize] + a[(n - 2) as usize] - a[(n - 1) as usize];
    let y = a[(n - 3) as usize] - a[(n - 2) as usize] + a[(n - 1) as usize];
    let z = -a[(n - 3) as usize] + a[(n - 2) as usize] + a[(n - 1) as usize];
    if x <= 0 || y <= 0 || z <= 0 {
        return ((n - 2, n - 1, n), true);
    }

    proof {
        assert(sa[0] + sa[1] > sa[sa.len() - 1]) by {
            assert(sa[0] == a@[0] as int);
            assert(sa[1] == a@[1] as int);
            assert(sa[sa.len() - 1] == a@[a@.len() - 1] as int);
        }
        all_triangles_valid(sa);
    }
    ((0, 0, 0), false)
}

fn main() {}

} // verus!

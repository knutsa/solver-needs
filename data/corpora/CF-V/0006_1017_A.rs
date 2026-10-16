use vstd::prelude::*;

verus! {

// The total score for a student (sum of their 4 subject scores).
pub open spec fn total_score(student: Seq<int>) -> int
    recommends student.len() >= 4
{
    student[0] + student[1] + student[2] + student[3]
}

// Count how many students in the given sequence have a total score
// strictly greater than the threshold.
pub open spec fn count_better(students: Seq<Seq<int>>, threshold: int) -> int
    recommends forall|i: int| 0 <= i < students.len() ==> (#[trigger] students[i]).len() >= 4
    decreases students.len()
{
    if students.len() == 0 {
        0
    } else {
        count_better(students.take(students.len() as int - 1), threshold)
            + if total_score(students[students.len() as int - 1]) > threshold { 1 as int } else { 0 as int }
    }
}

// The rank of Thomas is 1 + the number of students who scored strictly higher.
pub open spec fn expected_rank(n: int, scores: Seq<Seq<int>>) -> int
    recommends
        n >= 1,
        scores.len() >= n,
        forall|i: int| 0 <= i < n ==> (#[trigger] scores[i]).len() >= 4,
{
    1 + count_better(scores.subrange(1, n), total_score(scores[0]))
}

pub fn the_rank(n: i64, scores: &Vec<Vec<i64>>) -> (rank: i64)
    requires
        n >= 1,
        scores.len() >= n,
        forall|i: int| 0 <= i < n ==> (#[trigger] scores@[i]).len() >= 4,
        // Bounds to prevent overflow
        forall|i: int, j: int| 0 <= i < n && 0 <= j < scores@[i].len() ==>
            -1_000_000 <= (#[trigger] scores@[i][j]) <= 1_000_000,
    ensures
        rank == expected_rank(n as int, scores@.map(|_idx: int, v: Vec<i64>| v@.map(|_j: int, x: i64| x as int)))
{
    let ghost scores_int: Seq<Seq<int>> = scores@.map(|_idx: int, v: Vec<i64>| v@.map(|_j: int, x: i64| x as int));

    let my_score: i64 = scores[0][0] + scores[0][1] + scores[0][2] + scores[0][3];

    assert(my_score as int == total_score(scores_int[0]));

    let mut rank: i64 = 1;
    let mut i: i64 = 1;

    while i < n
        invariant
            1 <= i <= n,
            n >= 1,
            scores.len() >= n,
            forall|k: int| 0 <= k < n ==> (#[trigger] scores@[k]).len() >= 4,
            forall|k: int, j: int| 0 <= k < n && 0 <= j < scores@[k].len() ==>
                -1_000_000 <= (#[trigger] scores@[k][j]) <= 1_000_000,
            scores_int == scores@.map(|_idx: int, v: Vec<i64>| v@.map(|_j: int, x: i64| x as int)),
            my_score as int == total_score(scores_int[0]),
            rank as int == 1 + count_better(scores_int.subrange(1, i as int), my_score as int),
            0 <= count_better(scores_int.subrange(1, i as int), my_score as int) <= i - 1,
            1 <= rank <= i,
        decreases n - i,
    {
        let other_score: i64 = scores[i as usize][0] + scores[i as usize][1] + scores[i as usize][2] + scores[i as usize][3];

        // Key assertion: subrange(1, i+1) extended by one element
        // scores_int.subrange(1, i+1) == scores_int.subrange(1, i).push(scores_int[i])
        proof {
            let s1i = scores_int.subrange(1, i as int);
            let s1i1 = scores_int.subrange(1, i as int + 1);
            let combined = s1i.push(scores_int[i as int]);

            // Show s1i1 == combined
            assert(s1i1.len() == combined.len());
            assert forall|k: int| 0 <= k < s1i1.len() implies #[trigger] s1i1[k] =~= combined[k] by {
                if k < s1i.len() {
                    assert(s1i1[k] =~= scores_int[k + 1]);
                    assert(combined[k] =~= s1i[k]);
                    assert(s1i[k] =~= scores_int[k + 1]);
                } else {
                    assert(s1i1[k] =~= scores_int[k + 1]);
                    assert(combined[k] =~= scores_int[i as int]);
                    assert(k == i as int - 1);
                }
            }
            assert(s1i1 =~= combined);

            // Now show count_better unfolds correctly on combined = s1i.push(scores_int[i])
            assert(combined.len() > 0);
            assert(combined.take(combined.len() as int - 1) =~= s1i);
            assert(combined[combined.len() as int - 1] =~= scores_int[i as int]);
        }

        assert(other_score as int == total_score(scores_int[i as int]));

        if other_score > my_score {
            rank = rank + 1;
        }
        i = i + 1;
    }

    proof {
        assert(scores_int.subrange(1, n as int) =~= scores_int.subrange(1, i as int));
    }

    rank
}

fn main() {}

} // verus!

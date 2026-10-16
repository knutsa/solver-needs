use vstd::prelude::*;

verus! {

spec fn point_in_segment(p: int, seg: (int, int)) -> bool {
    seg.0 <= p && p <= seg.1
}

spec fn point_covered_by_any(p: int, segments: Seq<(int, int)>) -> bool {
    exists|i: int| 0 <= i < segments.len() && point_in_segment(p, segments[i])
}

spec fn strictly_increasing(s: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] < s[j]
}

spec fn to_spec_segments(segments: Seq<(i64, i64)>) -> Seq<(int, int)> {
    segments.map(|_idx, t: (i64, i64)| (t.0 as int, t.1 as int))
}

spec fn to_spec_result(result: Seq<i64>) -> Seq<int> {
    result.map(|_idx, v: i64| v as int)
}

proof fn lemma_si_append(s: Seq<int>, v: int)
    requires
        strictly_increasing(s),
        s.len() > 0 ==> s[s.len() - 1] < v,
    ensures
        strictly_increasing(s.push(v)),
{
    let new_s = s.push(v);
    assert forall|i: int, j: int| 0 <= i < j < new_s.len() implies new_s[i] < new_s[j]
    by {
        if j < s.len() {
            assert(new_s[i] == s[i]);
            assert(new_s[j] == s[j]);
        } else {
            // j == new_s.len() - 1
            assert(new_s[j] == v);
            if i < s.len() {
                assert(new_s[i] == s[i]);
                if s.len() > 1 {
                    // s[i] <= s[s.len()-1] < v
                    assert(s[i] < s[s.len() - 1]  ||  i == s.len() - 1);
                }
            }
        }
    }
}

fn points_in_segments(segments: &Vec<(i64, i64)>, m: i64) -> (result: Vec<i64>)
    requires
        m >= 0,
        m < i64::MAX / 2,
        segments.len() < usize::MAX,
        forall|i: int| 0 <= i < segments.len() ==> 1 <= segments[i].0 && segments[i].0 <= segments[i].1 && segments[i].1 <= m,
    ensures
        forall|i: int| 0 <= i < result.len() ==> 1 <= result[i] && result[i] <= m,
        forall|i: int| 0 <= i < result.len() ==> !point_covered_by_any(result[i] as int, to_spec_segments(segments@)),
        forall|p: int| 1 <= p <= m ==> !(#[trigger] point_covered_by_any(p, to_spec_segments(segments@))) ==>
            exists|j: int| 0 <= j < result.len() && result[j] == p,
        strictly_increasing(to_spec_result(result@)),
{
    let ghost seg_spec: Seq<(int, int)> = to_spec_segments(segments@);

    // Initialize A to all true
    let mut a_vec: Vec<bool> = Vec::new();
    let mut idx: i64 = 0;
    while idx < m
        invariant
            0 <= idx <= m,
            m >= 0,
            m < i64::MAX / 2,
            a_vec.len() == idx as int,
            forall|k: int| 0 <= k < idx as int ==> a_vec[k] == true,
        decreases m - idx,
    {
        a_vec.push(true);
        idx = idx + 1;
    }
    assert(a_vec.len() == m as int);

    // For each segment, mark covered positions as false
    let mut i: usize = 0;
    while i < segments.len()
        invariant
            0 <= i <= segments.len(),
            a_vec.len() == m as int,
            seg_spec =~= to_spec_segments(segments@),
            m >= 0,
            m < i64::MAX / 2,
            segments.len() < usize::MAX,
            forall|ii: int| #![auto] 0 <= ii < segments.len() ==> 1 <= segments[ii].0 && segments[ii].0 <= segments[ii].1 && segments[ii].1 <= m,
            forall|p: int| #![auto] 0 <= p < m ==>
                (a_vec[p] <==> forall|idx2: int| 0 <= idx2 < i ==> !point_in_segment(p + 1, seg_spec[idx2])),
        decreases segments.len() - i,
    {
        let seg_a: i64 = segments[i].0;
        let seg_b: i64 = segments[i].1;
        let ghost a_before: Seq<bool> = a_vec@;

        assert(1 <= seg_a && seg_a <= seg_b && seg_b <= m);

        let mut j: i64 = seg_a - 1;  // seg_a >= 1, so no underflow
        while j < seg_b
            invariant
                seg_a - 1 <= j <= seg_b,
                a_vec.len() == m as int,
                a_before.len() == m as int,
                0 <= i < segments.len(),
                1 <= seg_a <= seg_b <= m,
                m < i64::MAX / 2,
                seg_a == segments[i as int].0,
                seg_b == segments[i as int].1,
                seg_spec =~= to_spec_segments(segments@),
                forall|p: int| #![auto] 0 <= p < m && seg_a - 1 <= p && p < j ==> a_vec[p] == false,
                forall|p: int| #![auto] 0 <= p < m && !(seg_a - 1 <= p && p < j) ==> a_vec[p] == a_before[p],
                forall|p: int| #![auto] 0 <= p < m ==>
                    (a_before[p] <==> forall|idx2: int| 0 <= idx2 < i ==> !point_in_segment(p + 1, seg_spec[idx2])),
            decreases seg_b - j,
        {
            if 0 <= j && j < m {
                a_vec.set(j as usize, false);
            }
            j = j + 1;
        }

        // Forall proof: after processing segment i, the invariant holds for i+1
        assert forall|p: int| #![auto] 0 <= p < m implies
            (a_vec[p] <==> forall|idx2: int| 0 <= idx2 < (i + 1) as int ==> !point_in_segment(p + 1, seg_spec[idx2]))
        by {
            if seg_a - 1 <= p && p < seg_b {
                // p is in segment i's range, so a_vec[p] is false
                assert(a_vec[p] == false);
                assert(point_in_segment(p + 1, seg_spec[i as int]));
                // so !(forall idx2 :: ... ==> !PointInSegment)  since idx2=i fails
            } else {
                // p is not in segment i's range
                assert(!point_in_segment(p + 1, seg_spec[i as int]));
                assert(a_vec[p] == a_before[p]);
                // a_before[p] <==> forall idx2 < i ==> !PointInSegment
                // and !PointInSegment(p+1, seg[i]), so the forall extends to i+1
            }
        }

        i = i + 1;
    }

    // Forall proof: A[p] <==> !PointCoveredByAny(p+1, segments)
    assert forall|p: int| 0 <= p < m implies
        (a_vec[p] <==> !point_covered_by_any(p + 1, seg_spec))
    by {
        // From invariant: a_vec[p] <==> forall idx2 :: 0 <= idx2 < |segments| ==> !PointInSegment(p+1, seg[idx2])
        // The negation of the forall is: exists idx2 :: 0 <= idx2 < |segments| && PointInSegment(p+1, seg[idx2])
        // Which is point_covered_by_any(p+1, seg_spec)
        assert(a_vec[p] <==> forall|idx2: int| 0 <= idx2 < segments@.len() ==> !point_in_segment(p + 1, seg_spec[idx2]));
    }

    // Build result: collect uncovered points in order
    let mut result: Vec<i64> = Vec::new();
    let mut k: i64 = 0;
    while k < m
        invariant
            0 <= k <= m,
            a_vec.len() == m as int,
            m >= 0,
            m < i64::MAX / 2,
            seg_spec =~= to_spec_segments(segments@),
            forall|p: int| #![auto] 0 <= p < m ==> (a_vec[p] <==> !point_covered_by_any(p + 1, seg_spec)),
            forall|q: int| 0 <= q < result.len() ==> 1 <= result[q] && result[q] <= m,
            forall|q: int| 0 <= q < result.len() ==> !point_covered_by_any(result[q] as int, seg_spec),
            forall|p: int| 1 <= p <= k ==> !(#[trigger] point_covered_by_any(p, seg_spec)) ==>
                exists|q: int| 0 <= q < result.len() && result[q] == p,
            strictly_increasing(to_spec_result(result@)),
            result.len() > 0 ==> result[result.len() - 1] <= k,
        decreases m - k,
    {
        let ghost old_result: Seq<i64> = result@;
        if a_vec[k as usize] {
            // Prove strictly_increasing is maintained after appending k+1
            proof {
                let old_s = to_spec_result(result@);
                if result@.len() > 0 {
                    assert(result[result@.len() - 1] <= k);
                    assert(old_s[old_s.len() - 1] <= k as int);
                    assert(old_s[old_s.len() - 1] < (k + 1) as int);
                }
                lemma_si_append(old_s, (k + 1) as int);
                // Need to show to_spec_result(result@.push(k+1)) == old_s.push(k+1)
                assert(to_spec_result(result@.push((k + 1) as i64)) =~= old_s.push((k + 1) as int));
            }
            result.push(k + 1);
        }

        // Prove completeness for the new value of k (k+1)
        proof {
            // First establish result is a supersequence of old_result
            assert forall|q: int| 0 <= q < old_result.len() implies result[q] == old_result[q]
            by {
                if a_vec@[k as int] {
                    assert(result@ =~= old_result.push((k + 1) as i64));
                } else {
                    assert(result@ =~= old_result);
                }
            }

            // Now prove: for all p with 1 <= p <= k+1, if !covered(p) then exists q...
            assert forall|p: int| 1 <= p <= k + 1 && !(#[trigger] point_covered_by_any(p, seg_spec))
                implies exists|q: int| 0 <= q < result.len() && result[q] == p
            by {
                if p <= k {
                    // From old invariant
                    let q_old = choose|q: int| 0 <= q < old_result.len() && old_result[q] == p;
                    assert(0 <= q_old < result.len());
                    assert(result[q_old] == p);
                } else {
                    // p == k + 1
                    assert(a_vec[k as int] == true);  // because !covered(p) and a_vec <==> !covered
                    // We entered the if branch and pushed k+1
                    assert(result[result.len() - 1] == (k + 1) as i64);
                    assert(result[result.len() - 1] == p);
                }
            }
        }

        k = k + 1;
    }

    result
}

fn main() {}

} // verus!

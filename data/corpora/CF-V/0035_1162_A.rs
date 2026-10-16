use vstd::prelude::*;

verus! {

// Ghost type for restrictions
type GhostRestriction = (int, int, int);

// Helper: convert exec seq to ghost seq of ints
spec fn to_int_seq(s: Seq<i64>) -> Seq<int>
{
    s.map_values(|x: i64| x as int)
}

// A height assignment is valid: all heights in [0, h] and all zoning restrictions satisfied
spec fn is_valid_assignment(a: Seq<int>, n: int, h: int, restrictions: Seq<GhostRestriction>) -> bool
    recommends n >= 0
{
    a.len() == n &&
    (forall|i: int| 0 <= i < n ==> 0 <= #[trigger] a[i] <= h) &&
    (forall|k: int| #![trigger restrictions[k]] 0 <= k < restrictions.len() ==>
        forall|j: int| restrictions[k].0 - 1 <= j < restrictions[k].1 ==>
            (0 <= j < n ==> a[j] <= restrictions[k].2))
}

// Total profit: sum of squared heights
spec fn profit(a: Seq<int>) -> int
    decreases a.len()
{
    if a.len() == 0 {
        0
    } else {
        profit(a.subrange(0, a.len() - 1)) + a[a.len() - 1] * a[a.len() - 1]
    }
}

// Maximum allowed height at 0-indexed position i
spec fn effective_cap(i: int, h: int, restrictions: Seq<GhostRestriction>) -> int
    decreases restrictions.len()
{
    if restrictions.len() == 0 {
        h
    } else {
        let prev = effective_cap(i, h, restrictions.subrange(0, restrictions.len() - 1));
        let r = restrictions[restrictions.len() - 1];
        if r.0 - 1 <= i < r.1 && r.2 < prev {
            r.2
        } else {
            prev
        }
    }
}

// The profit-maximizing assignment: each position gets its maximum allowed height
spec fn optimal_assignment(n: int, h: int, restrictions: Seq<GhostRestriction>) -> Seq<int>
    decreases n
{
    if n <= 0 {
        Seq::empty()
    } else {
        optimal_assignment(n - 1, h, restrictions).push(effective_cap(n - 1, h, restrictions))
    }
}

// EffectiveCap is tightest: check for a specific value v
spec fn respects_all_restrictions(i: int, v: int, restrictions: Seq<GhostRestriction>) -> bool
{
    forall|k: int| 0 <= k < restrictions.len() ==>
        (restrictions[k].0 - 1 <= i < restrictions[k].1 ==> v <= #[trigger] restrictions[k].2)
}

// EffectiveCap is tightest: any value satisfying all restrictions is <= effective_cap
spec fn effective_cap_is_tightest(i: int, h: int, restrictions: Seq<GhostRestriction>) -> bool
{
    forall|v: int|
        #![trigger respects_all_restrictions(i, v, restrictions)]
        0 <= v <= h && respects_all_restrictions(i, v, restrictions)
        ==> v <= effective_cap(i, h, restrictions)
}

// Helper: convert exec restrictions to ghost
spec fn to_ghost_restrictions(r: Seq<(i64, i64, i64)>) -> Seq<GhostRestriction>
{
    r.map_values(|t: (i64, i64, i64)| (t.0 as int, t.1 as int, t.2 as int))
}

// ===== Helper Lemmas =====

proof fn optimal_assignment_length(n: int, h: int, restrictions: Seq<GhostRestriction>)
    requires n >= 0,
    ensures optimal_assignment(n, h, restrictions).len() == n,
    decreases n,
{
    if n > 0 {
        optimal_assignment_length(n - 1, h, restrictions);
    }
}

proof fn optimal_assignment_index(n: int, h: int, restrictions: Seq<GhostRestriction>, idx: int)
    requires
        n >= 0,
        0 <= idx < n,
    ensures
        optimal_assignment(n, h, restrictions).len() == n,
        optimal_assignment(n, h, restrictions)[idx] == effective_cap(idx, h, restrictions),
    decreases n,
{
    optimal_assignment_length(n, h, restrictions);
    if idx < n - 1 {
        optimal_assignment_index(n - 1, h, restrictions, idx);
    } else {
        optimal_assignment_length(n - 1, h, restrictions);
    }
}

proof fn effective_cap_range(pos: int, h: int, restrictions: Seq<GhostRestriction>)
    requires
        h >= 0,
        forall|k: int| 0 <= k < restrictions.len() ==> #[trigger] restrictions[k].2 >= 0,
    ensures
        0 <= effective_cap(pos, h, restrictions) <= h,
    decreases restrictions.len(),
{
    if restrictions.len() > 0 {
        effective_cap_range(pos, h, restrictions.subrange(0, restrictions.len() - 1));
    }
}

proof fn effective_cap_step(pos: int, h: int, restrictions: Seq<GhostRestriction>, k: int)
    requires 0 <= k < restrictions.len(),
    ensures
        effective_cap(pos, h, restrictions.subrange(0, k + 1)) ==
            (if restrictions[k].0 - 1 <= pos < restrictions[k].1 &&
                restrictions[k].2 < effective_cap(pos, h, restrictions.subrange(0, k))
             { restrictions[k].2 }
             else { effective_cap(pos, h, restrictions.subrange(0, k)) }),
{
    assert(restrictions.subrange(0, k + 1).subrange(0, (restrictions.subrange(0, k + 1).len() - 1) as int)
        =~= restrictions.subrange(0, k));
}

proof fn effective_cap_monotone(pos: int, h: int, restrictions: Seq<GhostRestriction>)
    requires restrictions.len() > 0,
    ensures effective_cap(pos, h, restrictions) <= effective_cap(pos, h, restrictions.subrange(0, restrictions.len() - 1)),
{
}

proof fn effective_cap_respects_restriction(pos: int, h: int, restrictions: Seq<GhostRestriction>, k: int)
    requires
        h >= 0,
        0 <= k < restrictions.len(),
        forall|m: int| 0 <= m < restrictions.len() ==> #[trigger] restrictions[m].2 >= 0,
        restrictions[k].0 - 1 <= pos < restrictions[k].1,
    ensures
        effective_cap(pos, h, restrictions) <= restrictions[k].2,
    decreases restrictions.len(),
{
    if restrictions.len() > 1 && k < restrictions.len() - 1 {
        effective_cap_respects_restriction(pos, h, restrictions.subrange(0, restrictions.len() - 1), k);
        effective_cap_monotone(pos, h, restrictions);
    }
}

proof fn effective_cap_tightest(pos: int, h: int, restrictions: Seq<GhostRestriction>, v: int)
    requires
        0 <= v <= h,
        forall|k: int| 0 <= k < restrictions.len() ==>
            (restrictions[k].0 - 1 <= pos < restrictions[k].1 ==> v <= #[trigger] restrictions[k].2),
    ensures
        v <= effective_cap(pos, h, restrictions),
    decreases restrictions.len(),
{
    if restrictions.len() > 0 {
        effective_cap_tightest(pos, h, restrictions.subrange(0, restrictions.len() - 1), v);
    }
}

proof fn profit_bound(a: Seq<int>, h: int)
    requires
        h >= 0,
        forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= h,
    ensures
        0 <= profit(a) <= a.len() * h * h,
    decreases a.len(),
{
    if a.len() > 0 {
        let prefix = a.subrange(0, a.len() - 1);
        assert forall|i: int| 0 <= i < prefix.len() implies 0 <= #[trigger] prefix[i] <= h by {
            assert(prefix[i] == a[i]);
        }
        profit_bound(prefix, h);
        assert(a[a.len() - 1] * a[a.len() - 1] <= h * h) by(nonlinear_arith)
            requires 0 <= a[a.len() - 1 as int] <= h;
        assert(profit(a) == profit(prefix) + a[a.len() - 1] * a[a.len() - 1]);
        assert((a.len() - 1) * h * h + h * h == a.len() * h * h) by(nonlinear_arith)
            requires a.len() > 0;
    }
}

proof fn profit_append(s: Seq<int>, x: int)
    ensures profit(s.push(x)) == profit(s) + x * x,
{
    let t = s.push(x);
    assert(t.subrange(0, t.len() - 1) =~= s);
}

// Lemma: to_int_seq preserves length and indexing
proof fn to_int_seq_len(s: Seq<i64>)
    ensures
        to_int_seq(s).len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> #[trigger] to_int_seq(s)[i] == s[i] as int,
{
}

// Lemma: to_int_seq of subrange
proof fn to_int_seq_subrange(s: Seq<i64>, lo: int, hi: int)
    requires 0 <= lo <= hi <= s.len(),
    ensures to_int_seq(s).subrange(lo, hi) =~= to_int_seq(s.subrange(lo, hi)),
{
    assert forall|i: int| 0 <= i < hi - lo implies
        #[trigger] to_int_seq(s).subrange(lo, hi)[i] == to_int_seq(s.subrange(lo, hi))[i]
    by {}
}

// Lemma: to_int_seq of push
proof fn to_int_seq_push(s: Seq<i64>, x: i64)
    ensures to_int_seq(s.push(x)) =~= to_int_seq(s).push(x as int),
{
}

// ===== Main Method =====

fn zoning_restrictions(n: i64, h: i64, m: i64, restrictions: &Vec<(i64, i64, i64)>) -> (max_profit: i64)
    requires
        n >= 0,
        h >= 0,
        n <= 1000, // bounds for overflow safety
        h <= 1000,
        forall|k: int| 0 <= k < restrictions@.len() ==>
            1 <= (#[trigger] restrictions@[k]).0 <= restrictions@[k].1 <= n &&
            restrictions@[k].2 >= 0 && restrictions@[k].2 <= 1000,
    ensures
    ({
        let gr = to_ghost_restrictions(restrictions@);
        let opt = optimal_assignment(n as int, h as int, gr);
        &&& is_valid_assignment(opt, n as int, h as int, gr)
        &&& max_profit == profit(opt)
        &&& (forall|i: int|
                #![trigger effective_cap(i, h as int, gr)]
                0 <= i < n ==> effective_cap_is_tightest(i, h as int, gr))
    }),
{
    let ghost gr = to_ghost_restrictions(restrictions@);

    // Prove to_ghost_restrictions preserves length and values
    proof {
        assert(gr.len() == restrictions@.len());
        assert forall|k: int| 0 <= k < gr.len() implies #[trigger] gr[k] == (restrictions@[k].0 as int, restrictions@[k].1 as int, restrictions@[k].2 as int) by {}
    }

    let mut ans: Vec<i64> = Vec::new();

    // Loop 1: Initialize all heights to h
    let mut i: usize = 0;
    while i < n as usize
        invariant
            0 <= i <= n,
            n >= 0,
            h >= 0,
            h <= 1000,
            ans@.len() == i as int,
            forall|j: int| 0 <= j < i as int ==> #[trigger] ans@[j] == h,
        decreases n - i,
    {
        ans.push(h);
        i = i + 1;
    }

    // Transition: EffectiveCap(j, h, []) == h
    proof {
        assert(gr.subrange(0, 0) =~= Seq::<GhostRestriction>::empty());
        assert forall|j: int| 0 <= j < n implies ans@[j] as int == effective_cap(j, h as int, gr.subrange(0, 0)) by {}
    }

    // Loop 2: Apply each restriction
    let mut ii: usize = 0;
    while ii < restrictions.len()
        invariant
            0 <= ii <= restrictions@.len(),
            ans@.len() == n,
            n >= 0,
            h >= 0,
            n <= 1000,
            h <= 1000,
            gr == to_ghost_restrictions(restrictions@),
            gr.len() == restrictions@.len(),
            forall|k: int| 0 <= k < gr.len() ==> #[trigger] gr[k] == (restrictions@[k].0 as int, restrictions@[k].1 as int, restrictions@[k].2 as int),
            forall|k: int| 0 <= k < restrictions@.len() ==>
                1 <= (#[trigger] restrictions@[k]).0 <= restrictions@[k].1 <= n &&
                restrictions@[k].2 >= 0 && restrictions@[k].2 <= 1000,
            forall|j: int| 0 <= j < n ==> #[trigger] ans@[j] as int == effective_cap(j, h as int, gr.subrange(0, ii as int)),
            forall|j: int| 0 <= j < n ==> 0 <= #[trigger] ans@[j] <= h,
        decreases restrictions@.len() - ii,
    {
        let l = restrictions[ii].0;
        let r = restrictions[ii].1;
        let x = restrictions[ii].2;

        let mut j: i64 = l - 1;

        while j < r
            invariant
                l - 1 <= j <= r,
                l == restrictions@[ii as int].0,
                r == restrictions@[ii as int].1,
                x == restrictions@[ii as int].2,
                0 <= ii < restrictions@.len(),
                ans@.len() == n,
                n >= 0,
                h >= 0,
                n <= 1000,
                h <= 1000,
                x >= 0,
                x <= 1000,
                1 <= l <= r <= n,
                gr == to_ghost_restrictions(restrictions@),
                gr.len() == restrictions@.len(),
                forall|k: int| 0 <= k < gr.len() ==> #[trigger] gr[k] == (restrictions@[k].0 as int, restrictions@[k].1 as int, restrictions@[k].2 as int),
                forall|k: int| 0 <= k < restrictions@.len() ==>
                    1 <= (#[trigger] restrictions@[k]).0 <= restrictions@[k].1 <= n &&
                    restrictions@[k].2 >= 0 && restrictions@[k].2 <= 1000,
                forall|pos: int| 0 <= pos < n && !(l - 1 <= pos < r) ==>
                    #[trigger] ans@[pos] as int == effective_cap(pos, h as int, gr.subrange(0, ii as int)),
                forall|pos: int| 0 <= pos < n && l - 1 <= pos < j ==>
                    #[trigger] ans@[pos] as int == effective_cap(pos, h as int, gr.subrange(0, (ii + 1) as int)),
                forall|pos: int| 0 <= pos < n && j <= pos < r ==>
                    #[trigger] ans@[pos] as int == effective_cap(pos, h as int, gr.subrange(0, ii as int)),
                forall|pos: int| 0 <= pos < n ==> 0 <= #[trigger] ans@[pos] <= h,
            decreases r - j,
        {
            proof {
                effective_cap_step(j as int, h as int, gr, ii as int);
                assert(gr[ii as int].0 - 1 <= j < gr[ii as int].1);
            }
            if ans[j as usize] > x {
                ans.set(j as usize, x);
            }
            j = j + 1;
        }

        // Unify: for positions outside [l-1, r), EffectiveCap is unchanged
        proof {
            assert forall|pos: int| 0 <= pos < n implies
                #[trigger] ans@[pos] as int == effective_cap(pos, h as int, gr.subrange(0, (ii + 1) as int))
            by {
                if !(l - 1 <= pos < r) {
                    effective_cap_step(pos, h as int, gr, ii as int);
                }
            }
        }

        ii = ii + 1;
    }

    proof {
        assert(gr.subrange(0, gr.len() as int) =~= gr);
        assert forall|j: int| 0 <= j < n implies ans@[j] as int == effective_cap(j, h as int, gr) by {}
    }

    // Prove ans matches OptimalAssignment
    proof {
        let opt = optimal_assignment(n as int, h as int, gr);
        optimal_assignment_length(n as int, h as int, gr);

        assert forall|j: int| 0 <= j < n implies ans@[j] as int == #[trigger] opt[j] by {
            optimal_assignment_index(n as int, h as int, gr, j);
        }
        assert(to_int_seq(ans@) =~= opt);
    }

    // Loop 3: Compute total profit
    let ghost saved_ans = ans@;
    let mut temp: i64 = 0;
    i = 0;
    while i < n as usize
        invariant
            0 <= i <= n,
            n >= 0,
            h >= 0,
            n <= 1000,
            h <= 1000,
            ans@.len() == n,
            ans@ == saved_ans,
            temp == profit(to_int_seq(ans@).subrange(0, i as int)),
            forall|j: int| 0 <= j < n ==> 0 <= #[trigger] ans@[j] <= h,
            // overflow bound: profit is bounded by i * h * h <= 1000 * 1000 * 1000
            0 <= temp <= i * h * h,
        decreases n - i,
    {
        proof {
            to_int_seq_subrange(ans@, 0, i as int);
            let gs = to_int_seq(ans@).subrange(0, i as int);
            assert forall|j: int| 0 <= j < gs.len() implies 0 <= #[trigger] gs[j] <= h by {
                assert(gs[j] == to_int_seq(ans@)[j]);
            }
            profit_bound(gs, h as int);
            profit_append(to_int_seq(ans@).subrange(0, i as int), ans@[i as int] as int);
            assert(to_int_seq(ans@).subrange(0, i as int).push(ans@[i as int] as int)
                =~= to_int_seq(ans@).subrange(0, (i + 1) as int));
            // Bound after append
            let gs2 = to_int_seq(ans@).subrange(0, (i + 1) as int);
            assert forall|j: int| 0 <= j < gs2.len() implies 0 <= #[trigger] gs2[j] <= h by {
                assert(gs2[j] == to_int_seq(ans@)[j]);
            }
            profit_bound(gs2, h as int);
            assert((i + 1) * h * h <= (i + 1) * (h * h)) by(nonlinear_arith)
                requires i >= 0int, h >= 0int;
            assert((i + 1) * (h * h) <= (n as int) * (h * h)) by(nonlinear_arith)
                requires i + 1 <= n, h * h >= 0;
        }
        let val = ans[i];
        assert(0 <= val <= h);
        assert(0 <= val <= 1000);
        assert(val * val <= 1_000_000) by(nonlinear_arith)
            requires 0 <= val <= 1000i64;
        assert(0 <= temp <= 999_000_000) by {
            assert(i * h * h <= 999 * 1000 * 1000) by(nonlinear_arith)
                requires 0 <= i <= 999int, 0 <= h <= 1000int;
        }
        temp = temp + val * val;
        i = i + 1;
    }

    proof {
        assert(to_int_seq(ans@).subrange(0, n as int) =~= to_int_seq(ans@));
        let opt = optimal_assignment(n as int, h as int, gr);
        assert(to_int_seq(ans@) =~= opt);
    }

    let max_profit = temp;

    // Prove ensures: IsValidAssignment
    proof {
        let opt = optimal_assignment(n as int, h as int, gr);
        assert(to_int_seq(ans@) =~= opt);

        assert forall|idx: int| 0 <= idx < n implies 0 <= #[trigger] opt[idx] <= h by {
            optimal_assignment_index(n as int, h as int, gr, idx);
            effective_cap_range(idx, h as int, gr);
        }

        assert forall|k: int| #![trigger gr[k]] 0 <= k < gr.len() implies
            forall|j: int| gr[k].0 - 1 <= j < gr[k].1 ==>
                (0 <= j < n ==> opt[j] <= gr[k].2)
        by {
            assert forall|j: int| gr[k].0 - 1 <= j < gr[k].1 implies
                (0 <= j < n ==> opt[j] <= gr[k].2)
            by {
                if 0 <= j < n {
                    optimal_assignment_index(n as int, h as int, gr, j);
                    effective_cap_respects_restriction(j, h as int, gr, k);
                }
            }
        }

        // Prove ensures: EffectiveCap is the tightest upper bound
        assert forall|i: int|
            #![trigger effective_cap(i, h as int, gr)]
            0 <= i < n implies effective_cap_is_tightest(i, h as int, gr)
        by {
            // Unfold effective_cap_is_tightest
            assert forall|v: int|
                #![trigger respects_all_restrictions(i, v, gr)]
                0 <= v <= h && respects_all_restrictions(i, v, gr)
                implies v <= effective_cap(i, h as int, gr)
            by {
                effective_cap_tightest(i, h as int, gr, v);
            }
        }
    }

    max_profit
}

} // verus!

fn main() {}

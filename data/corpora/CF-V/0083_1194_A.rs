use vstd::prelude::*;

verus! {

spec fn initial_list(n: nat) -> Seq<int>
    decreases n,
{
    if n == 0 { Seq::<int>::empty() } else { initial_list((n - 1) as nat).push(n as int) }
}

spec fn remove_at_index(s: Seq<int>, idx: nat) -> Seq<int>
    recommends idx < s.len(),
{
    s.take(idx as int).add(s.skip(idx as int + 1))
}

spec fn simulate(remaining: Seq<int>, step: nat) -> Seq<int>
    decreases remaining.len(),
{
    if step == 0 || step > remaining.len() {
        remaining
    } else {
        simulate(remove_at_index(remaining, (step - 1) as nat), (step + 1) as nat)
    }
}

spec fn final_list(n: nat) -> Seq<int> {
    simulate(initial_list(n), 1)
}

spec fn even_list(k: nat) -> Seq<int>
    decreases k,
{
    if k == 0 { Seq::<int>::empty() } else { even_list((k - 1) as nat).push(2 * k as int) }
}

spec fn range_seq(a: int, b: int) -> Seq<int>
    decreases (if b >= a { b - a + 1 } else { 0 }) as nat,
{
    if a > b { Seq::<int>::empty() } else { Seq::<int>::empty().push(a).add(range_seq(a + 1, b)) }
}

proof fn even_list_length(k: nat)
    ensures even_list(k).len() == k,
    decreases k,
{
    if k > 0 {
        even_list_length((k - 1) as nat);
    }
}

proof fn even_list_element(k: nat, i: nat)
    requires i < k,
    ensures
        even_list(k).len() == k,
        even_list(k)[i as int] == 2 * (i as int + 1),
    decreases k,
{
    even_list_length(k);
    if i < k - 1 {
        even_list_element((k - 1) as nat, i);
    }
}

proof fn range_seq_length(a: int, b: int)
    ensures range_seq(a, b).len() == (if a > b { 0 } else { b - a + 1 }),
    decreases (if b >= a { b - a + 1 } else { 0 }) as nat,
{
    if a <= b {
        range_seq_length(a + 1, b);
    }
}

proof fn range_seq_append(a: int, b: int)
    requires a <= b,
    ensures range_seq(a, b) =~= range_seq(a, b - 1).push(b),
    decreases (b - a) as nat,
{
    range_seq_length(a, b);
    range_seq_length(a, b - 1);
    if a < b {
        range_seq_append(a + 1, b);
    }
}

proof fn initial_list_equals_range(n: nat)
    ensures initial_list(n) =~= range_seq(1, n as int),
    decreases n,
{
    if n > 0 {
        initial_list_equals_range((n - 1) as nat);
        range_seq_append(1, n as int);
    }
}

proof fn remove_at_index_concat(s: Seq<int>, idx: nat)
    requires idx < s.len(),
    ensures remove_at_index(s, idx) =~= s.take(idx as int).add(s.skip(idx as int + 1)),
{
}

proof fn simulate_remove_at_index(remaining: Seq<int>, step: nat)
    requires
        step > 0,
        step <= remaining.len(),
    ensures
        simulate(remaining, step) == simulate(
            remove_at_index(remaining, (step - 1) as nat),
            (step + 1) as nat,
        ),
    decreases remaining.len(),
{
}

proof fn remove_at_index_len(s: Seq<int>, idx: nat)
    requires idx < s.len(),
    ensures remove_at_index(s, idx).len() == s.len() - 1,
{
}

proof fn simulate_from_state(k: nat, n: nat)
    requires 2 * k <= n,
    ensures simulate(even_list(k).add(range_seq(2 * k as int + 1, n as int)), (k + 1) as nat) =~= even_list((n / 2) as nat),
    decreases (n - 2 * k) as nat,
{
    even_list_length(k);
    range_seq_length(2 * k as int + 1, n as int);
    let state = even_list(k).add(range_seq(2 * k as int + 1, n as int));

    if 2 * k == n {
        // Base: range is empty, step > |state|, Simulate returns state
        assert(range_seq(2 * k as int + 1, n as int) =~= Seq::<int>::empty());
        assert(state =~= even_list(k));
        // step k+1 > |state| = k, so Simulate returns state
        assert(k + 1 > state.len());
        // Need to explicitly show simulate returns state when step > len
        assert(simulate(state, (k + 1) as nat) =~= state);
        assert(even_list((n / 2) as nat) =~= even_list(k));
    } else {
        // Inductive step: 2k < n, so step k+1 is valid
        assert(state.len() == n - k);
        assert(k + 1 <= n - k) by(nonlinear_arith)
            requires 2 * k < n;

        // Identify what's at index k (first element of the range suffix)
        assert(range_seq(2 * k as int + 1, n as int) =~=
            Seq::<int>::empty().push(2 * k as int + 1).add(range_seq(2 * k as int + 2, n as int)));

        assert(state.take(k as int) =~= even_list(k));
        assert(state.skip(k as int) =~= range_seq(2 * k as int + 1, n as int));
        assert(state.skip(k as int + 1) =~= range_seq(2 * k as int + 2, n as int));

        // After removing index k
        let after_removal = even_list(k).add(range_seq(2 * k as int + 2, n as int));
        assert(remove_at_index(state, k) =~= after_removal);

        // Show simulate unfolds: simulate(state, k+1) == simulate(remove_at_index(state, k), k+2)
        remove_at_index_len(state, k);
        assert(simulate(state, (k + 1) as nat) =~= simulate(remove_at_index(state, k), (k + 2) as nat));
        assert(simulate(state, (k + 1) as nat) =~= simulate(after_removal, (k + 2) as nat));

        if 2 * (k + 1) > n {
            // n = 2k+1 (odd): range becomes empty
            assert(range_seq(2 * k as int + 2, n as int) =~= Seq::<int>::empty());
            assert(after_removal =~= even_list(k));
            assert(n / 2 == k) by(nonlinear_arith)
                requires 2 * k < n, 2 * (k + 1) > n;
            // step k+2 > |after_removal| = k
            assert((k + 2) > after_removal.len());
            assert(simulate(after_removal, (k + 2) as nat) =~= after_removal);
        } else {
            // 2(k+1) <= n: fold 2k+2 into the even prefix
            assert(range_seq(2 * k as int + 2, n as int) =~=
                Seq::<int>::empty().push(2 * (k as int + 1)).add(range_seq(2 * (k as int + 1) + 1, n as int)));

            assert(even_list((k + 1) as nat) =~= even_list(k).push(2 * (k as int + 1)));
            assert(after_removal =~= even_list((k + 1) as nat).add(range_seq(2 * (k as int + 1) + 1, n as int)));

            simulate_from_state((k + 1) as nat, n);
        }
    }
}

proof fn final_list_is_even(n: nat)
    ensures final_list(n) =~= even_list((n / 2) as nat),
{
    initial_list_equals_range(n);
    assert(initial_list(n) =~= even_list(0).add(range_seq(1, n as int)));
    simulate_from_state(0, n);
}

fn remove_a_progression(n: i64, x: i64) -> (result: i64)
    requires
        n >= 1,
        x >= 1,
        x <= final_list(n as nat).len(),
    ensures result == final_list(n as nat)[(x - 1) as int],
{
    proof {
        final_list_is_even(n as nat);
        even_list_length((n as nat / 2) as nat);
        even_list_element((n as nat / 2) as nat, (x - 1) as nat);
    }
    x * 2
}

fn main() {}

} // verus!

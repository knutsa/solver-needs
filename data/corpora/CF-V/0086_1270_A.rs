use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

// ── Spec helpers ──────────────────────────────────────────────────────

pub open spec fn seq_to_set(s: Seq<int>) -> Set<int>
    decreases s.len(),
{
    if s.len() == 0 {
        Set::empty()
    } else {
        Set::empty().insert(s.last()).union(seq_to_set(s.take(s.len() as int - 1)))
    }
}

pub open spec fn no_duplicates(s: Seq<int>) -> bool {
    forall|i: int, j: int|
        0 <= i < j < s.len() ==> s[i] != s[j]
}

pub open spec fn valid_deck(n: int, a: Seq<int>, b: Seq<int>) -> bool {
    n >= 2
    && a.len() >= 1
    && b.len() >= 1
    && no_duplicates(a)
    && no_duplicates(b)
    && seq_to_set(a).disjoint(seq_to_set(b))
    && seq_to_set(a).union(seq_to_set(b)) =~= Set::new(|i: int| 1 <= i <= n)
}

pub open spec fn player1_can_win(s1: Set<int>, s2: Set<int>, steps: nat) -> bool
    decreases steps,
{
    if s2 =~= Set::empty() {
        true
    } else if s1 =~= Set::empty() || steps == 0 {
        false
    } else {
        exists|c1: int| #![trigger s1.contains(c1)]
            s1.contains(c1) && forall|c2: int| #![auto] s2.contains(c2) ==> {
                if c1 > c2 {
                    player1_can_win(s1.union(Set::empty().insert(c2)), s2.remove(c2), (steps - 1) as nat)
                } else {
                    player1_can_win(s1.remove(c1), s2.union(Set::empty().insert(c1)), (steps - 1) as nat)
                }
            }
    }
}

pub open spec fn player1_wins_game(s1: Set<int>, s2: Set<int>, bound: nat) -> bool {
    exists|steps: nat| player1_can_win(s1, s2, steps)
}

// ── Helper lemmas ─────────────────────────────────────────────────────

proof fn set_remove_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
        s.contains(a),
    ensures
        s.remove(a).len() == s.len() - 1,
{
    // follows from broadcast axiom_set_remove_len
}

pub proof fn seq_to_set_membership(s: Seq<int>, x: int)
    ensures
        seq_to_set(s).contains(x) <==> exists|k: int| 0 <= k < s.len() && s[k] == x,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        seq_to_set_membership(s.take(s.len() as int - 1), x);
        assert forall|k: int| 0 <= k < s.len() - 1 implies s.take(s.len() as int - 1)[k] == s[k] by {
        }
    }
}

proof fn seq_to_set_finite(s: Seq<int>)
    ensures
        seq_to_set(s).finite(),
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        seq_to_set_finite(s.take(s.len() as int - 1));
    }
}

pub proof fn player1_wins_with_max(s1: Set<int>, s2: Set<int>, m: int)
    requires
        s1.contains(m),
        s2.finite(),
        forall|x: int| s2.contains(x) ==> x < m,
    ensures
        player1_can_win(s1, s2, s2.len()),
    decreases s2.len(),
{
    if s2 =~= Set::empty() {
    } else {
        assert forall|c2: int| #![auto] s2.contains(c2) implies
            player1_can_win(s1.union(Set::empty().insert(c2)), s2.remove(c2), (s2.len() - 1) as nat)
        by {
            set_remove_len(s2, c2);
            assert(s2.remove(c2).len() < s2.len());
            player1_wins_with_max(s1.union(Set::empty().insert(c2)), s2.remove(c2), m);
        }
        // Witness: c1 = m
        assert(s1.contains(m));
        assert forall|c2: int| s2.contains(c2) implies m > c2 by {}
        // Show the body of the exists matches
        assert forall|c2: int| #![auto] s2.contains(c2) implies ({
            if m > c2 {
                player1_can_win(s1.union(Set::empty().insert(c2)), s2.remove(c2), (s2.len() - 1) as nat)
            } else {
                player1_can_win(s1.remove(m), s2.union(Set::empty().insert(m)), (s2.len() - 1) as nat)
            }
        }) by {}
    }
}

pub proof fn player1_loses_without_max(s1: Set<int>, s2: Set<int>, m: int, steps: nat)
    requires
        s2.contains(m),
        forall|x: int| s1.contains(x) ==> x < m,
    ensures
        !player1_can_win(s1, s2, steps),
    decreases steps,
{
    if s1 =~= Set::empty() || steps == 0 {
    } else {
        if player1_can_win(s1, s2, steps) {
            assert(!(s2 =~= Set::empty()));
            let c1 = choose|c1: int|
                #![trigger s1.contains(c1)]
                s1.contains(c1) && forall|c2: int| #![auto] s2.contains(c2) ==> {
                    if c1 > c2 {
                        player1_can_win(s1.union(Set::empty().insert(c2)), s2.remove(c2), (steps - 1) as nat)
                    } else {
                        player1_can_win(s1.remove(c1), s2.union(Set::empty().insert(c1)), (steps - 1) as nat)
                    }
                };
            assert(c1 < m);
            assert(s2.contains(m));
            assert(player1_can_win(s1.remove(c1), s2.union(Set::empty().insert(c1)), (steps - 1) as nat));
            player1_loses_without_max(s1.remove(c1), s2.union(Set::empty().insert(c1)), m, (steps - 1) as nat);
            assert(false);
        }
    }
}

// ── Method ────────────────────────────────────────────────────────────

pub fn card_game(n: i64, k1: i64, k2: i64, a: &Vec<i64>, b: &Vec<i64>) -> (first_player_wins: bool)
    requires
        valid_deck(n as int, a@.map_values(|x: i64| x as int), b@.map_values(|x: i64| x as int)),
        k1 == a.len(),
        k2 == b.len(),
    ensures
        first_player_wins <==> player1_wins_game(
            seq_to_set(a@.map_values(|x: i64| x as int)),
            seq_to_set(b@.map_values(|x: i64| x as int)),
            n as nat,
        ),
{
    let ghost a_spec = a@.map_values(|x: i64| x as int);
    let ghost b_spec = b@.map_values(|x: i64| x as int);

    let mut max_a: i64 = a[0];
    let mut i: usize = 1;
    proof {
        assert(a_spec[0] == a@[0] as int);
        assert(a@[0] == max_a);
        assert(a_spec[0] == max_a as int);
    }
    while i < a.len()
        invariant
            1 <= i <= a.len(),
            a_spec =~= a@.map_values(|x: i64| x as int),
            forall|k: int| #![auto] 0 <= k < i as int ==> a_spec[k] <= max_a as int,
            exists|k: int| 0 <= k < i as int && a_spec[k] == max_a as int,
        decreases a.len() - i,
    {
        proof {
            assert(a_spec[i as int] == a[i as int] as int);
        }
        if a[i] > max_a {
            max_a = a[i];
        }
        i = i + 1;
    }

    let mut max_b: i64 = b[0];
    let mut j: usize = 1;
    proof {
        assert(b_spec[0] == b@[0] as int);
        assert(b@[0] == max_b);
        assert(b_spec[0] == max_b as int);
    }
    while j < b.len()
        invariant
            1 <= j <= b.len(),
            b_spec =~= b@.map_values(|x: i64| x as int),
            forall|k: int| #![auto] 0 <= k < j as int ==> b_spec[k] <= max_b as int,
            exists|k: int| 0 <= k < j as int && b_spec[k] == max_b as int,
        decreases b.len() - j,
    {
        proof {
            assert(b_spec[j as int] == b[j as int] as int);
        }
        if b[j] > max_b {
            max_b = b[j];
        }
        j = j + 1;
    }

    let first_player_wins = max_a > max_b;

    proof {
        // Prove max_a exists in a_spec
        assert(exists|k: int| 0 <= k < a_spec.len() && a_spec[k] == max_a as int);
        seq_to_set_membership(a_spec, max_a as int);
        assert(seq_to_set(a_spec).contains(max_a as int));

        assert(exists|k: int| 0 <= k < b_spec.len() && b_spec[k] == max_b as int);
        seq_to_set_membership(b_spec, max_b as int);
        assert(seq_to_set(b_spec).contains(max_b as int));

        // All elements of a are <= maxA
        assert forall|x: int| seq_to_set(a_spec).contains(x) implies x <= max_a as int by {
            seq_to_set_membership(a_spec, x);
        }

        // All elements of b are <= maxB
        assert forall|x: int| seq_to_set(b_spec).contains(x) implies x <= max_b as int by {
            seq_to_set_membership(b_spec, x);
        }

        // maxA != maxB because disjoint sets
        assert(max_a as int != max_b as int);

        seq_to_set_finite(b_spec);

        if max_a > max_b {
            assert(forall|x: int| seq_to_set(b_spec).contains(x) ==> x < max_a as int);
            player1_wins_with_max(seq_to_set(a_spec), seq_to_set(b_spec), max_a as int);
            assert(player1_can_win(seq_to_set(a_spec), seq_to_set(b_spec), seq_to_set(b_spec).len()));
        } else {
            assert(max_b as int > max_a as int);
            assert(forall|x: int| seq_to_set(a_spec).contains(x) ==> x < max_b as int);
            assert forall|steps: nat|
                !player1_can_win(seq_to_set(a_spec), seq_to_set(b_spec), steps)
            by {
                player1_loses_without_max(seq_to_set(a_spec), seq_to_set(b_spec), max_b as int, steps);
            }
        }
    }

    first_player_wins
}

fn main() {}

} // verus!

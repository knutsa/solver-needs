use vstd::prelude::*;

verus! {

// The 13 valid ranks in the deck
pub open spec fn is_rank(c: char) -> bool {
    c == '2' || c == '3' || c == '4' || c == '5' || c == '6' ||
    c == '7' || c == '8' || c == '9' || c == 'T' || c == 'J' ||
    c == 'Q' || c == 'K' || c == 'A'
}

// The 4 valid suits in the deck
pub open spec fn is_suit(c: char) -> bool {
    c == 'D' || c == 'C' || c == 'S' || c == 'H'
}

// A valid card: exactly 2 characters, rank then suit
pub open spec fn is_card(s: Seq<char>) -> bool {
    s.len() == 2 && is_rank(s[0]) && is_suit(s[1])
}

// A valid Mau-Mau hand: exactly 5 valid cards
pub open spec fn is_hand(hand: Seq<Seq<char>>) -> bool {
    hand.len() == 5 && forall|i: int| 0 <= i < hand.len() ==> is_card(#[trigger] hand[i])
}

// The rank of a card (first character)
pub open spec fn rank_of(card: Seq<char>) -> char
    recommends card.len() >= 1
{
    card[0]
}

// The suit of a card (second character)
pub open spec fn suit_of(card: Seq<char>) -> char
    recommends card.len() >= 2
{
    card[1]
}

// A hand card is playable on a table card iff it shares rank or suit
pub open spec fn is_playable(hand_card: Seq<char>, table_card: Seq<char>) -> bool
    recommends hand_card.len() >= 2, table_card.len() >= 2
{
    rank_of(hand_card) == rank_of(table_card) || suit_of(hand_card) == suit_of(table_card)
}

// The player can make a move iff at least one card in hand is playable on the table card
pub open spec fn has_playable_card(hand: Seq<Seq<char>>, table_card: Seq<char>) -> bool
    recommends
        table_card.len() >= 2,
        forall|i: int| 0 <= i < hand.len() ==> (#[trigger] hand[i]).len() >= 2,
{
    exists|i: int| 0 <= i < hand.len() && is_playable(#[trigger] hand[i], table_card)
}

fn card_game(table: &Vec<char>, hand: &Vec<Vec<char>>) -> (can_play: bool)
    requires
        is_card(table@),
        is_hand(hand@.map(|_i: int, v: Vec<char>| v@)),
    ensures
        can_play == has_playable_card(hand@.map(|_i: int, v: Vec<char>| v@), table@),
{
    let mut can_play = false;
    let mut i: usize = 0;
    let ghost hand_spec: Seq<Seq<char>> = hand@.map(|_i: int, v: Vec<char>| v@);

    while i < hand.len()
        invariant
            0 <= i <= hand.len(),
            hand_spec =~= hand@.map(|_i: int, v: Vec<char>| v@),
            is_card(table@),
            is_hand(hand_spec),
            forall|j: int| 0 <= j < i ==> !is_playable(#[trigger] hand_spec[j], table@),
            !can_play,
        decreases hand.len() - i,
    {
        if hand[i].len() >= 2 && table.len() >= 2 {
            if hand[i][0] == table[0] || hand[i][1] == table[1] {
                can_play = true;
                assert(is_playable(hand_spec[i as int], table@));
                return can_play;
            }
        }
        i = i + 1;
    }
    // After the loop, no card was playable
    proof {
        let hs = hand@.map(|_i: int, v: Vec<char>| v@);
        assert(hand_spec =~= hs);
        assert forall|j: int| 0 <= j < hs.len() implies !is_playable(#[trigger] hs[j], table@) by {
            assert(hs[j] =~= hand_spec[j]);
        }
        assert(!has_playable_card(hs, table@));
    }
    assert(!has_playable_card(hand@.map(|_i: int, v: Vec<char>| v@), table@));
    can_play
}

fn main() {}

} // verus!

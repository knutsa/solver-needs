// --- Formal specification for Mau-Mau card game ---

// The 13 valid ranks in the deck
ghost predicate IsRank(c: char)
{
  c in {'2', '3', '4', '5', '6', '7', '8', '9', 'T', 'J', 'Q', 'K', 'A'}
}

// The 4 valid suits in the deck
ghost predicate IsSuit(c: char)
{
  c in {'D', 'C', 'S', 'H'}
}

// A valid card: exactly 2 characters, rank then suit
ghost predicate IsCard(s: string)
{
  |s| == 2 && IsRank(s[0]) && IsSuit(s[1])
}

// A valid Mau-Mau hand: exactly 5 valid cards
ghost predicate IsHand(hand: seq<string>)
{
  |hand| == 5 && forall i | 0 <= i < |hand| :: IsCard(hand[i])
}

// The rank of a card (first character)
ghost function RankOf(card: string): char
  requires |card| >= 1
{
  card[0]
}

// The suit of a card (second character)
ghost function SuitOf(card: string): char
  requires |card| >= 2
{
  card[1]
}

// A hand card is playable on a table card iff it shares rank or suit
ghost predicate IsPlayable(handCard: string, tableCard: string)
  requires |handCard| >= 2 && |tableCard| >= 2
{
  RankOf(handCard) == RankOf(tableCard) || SuitOf(handCard) == SuitOf(tableCard)
}

// The player can make a move iff at least one card in hand is playable on the table card
ghost predicate HasPlayableCard(hand: seq<string>, tableCard: string)
  requires |tableCard| >= 2
  requires forall i | 0 <= i < |hand| :: |hand[i]| >= 2
{
  exists i | 0 <= i < |hand| :: IsPlayable(hand[i], tableCard)
}

method CardGame(table: string, hand: seq<string>) returns (canPlay: bool)
  requires IsCard(table)
  requires IsHand(hand)
  ensures canPlay == HasPlayableCard(hand, table)
{
  canPlay := false;
  var i := 0;
  while i < |hand|
    invariant 0 <= i <= |hand|
    invariant forall j | 0 <= j < i :: !IsPlayable(hand[j], table)
  {
    if hand[i][0] == table[0] || hand[i][1] == table[1] {
      canPlay := true;
      return;
    }
    i := i + 1;
  }
}

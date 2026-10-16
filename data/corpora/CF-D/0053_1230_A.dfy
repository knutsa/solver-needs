ghost function FriendSum(a1: int, a2: int, a3: int, a4: int,
                   b1: bool, b2: bool, b3: bool, b4: bool): int
{
  (if b1 then a1 else 0) + (if b2 then a2 else 0) +
  (if b3 then a3 else 0) + (if b4 then a4 else 0)
}

ghost predicate CanDistributeEqually(a1: int, a2: int, a3: int, a4: int)
{
  exists b1: bool, b2: bool, b3: bool, b4: bool ::
    FriendSum(a1, a2, a3, a4, b1, b2, b3, b4) ==
    FriendSum(a1, a2, a3, a4, !b1, !b2, !b3, !b4)
}

method DawidAndCandies(a1: int, a2: int, a3: int, a4: int) returns (result: bool)
  requires a1 >= 1 && a2 >= 1 && a3 >= 1 && a4 >= 1
  ensures result == CanDistributeEqually(a1, a2, a3, a4)
{
  result := (a1 + a2 == a3 + a4) || (a1 + a3 == a2 + a4) || (a1 + a4 == a2 + a3) ||
            (a1 + a2 + a3 == a4) || (a1 + a2 + a4 == a3) || (a1 + a3 + a4 == a2) || (a2 + a3 + a4 == a1);

  if result {
    if a1 + a2 == a3 + a4 {
      assert FriendSum(a1, a2, a3, a4, true, true, false, false) ==
             FriendSum(a1, a2, a3, a4, false, false, true, true);
    } else if a1 + a3 == a2 + a4 {
      assert FriendSum(a1, a2, a3, a4, true, false, true, false) ==
             FriendSum(a1, a2, a3, a4, false, true, false, true);
    } else if a1 + a4 == a2 + a3 {
      assert FriendSum(a1, a2, a3, a4, true, false, false, true) ==
             FriendSum(a1, a2, a3, a4, false, true, true, false);
    } else if a1 + a2 + a3 == a4 {
      assert FriendSum(a1, a2, a3, a4, false, false, false, true) ==
             FriendSum(a1, a2, a3, a4, true, true, true, false);
    } else if a1 + a2 + a4 == a3 {
      assert FriendSum(a1, a2, a3, a4, false, false, true, false) ==
             FriendSum(a1, a2, a3, a4, true, true, false, true);
    } else if a1 + a3 + a4 == a2 {
      assert FriendSum(a1, a2, a3, a4, false, true, false, false) ==
             FriendSum(a1, a2, a3, a4, true, false, true, true);
    } else {
      assert a2 + a3 + a4 == a1;
      assert FriendSum(a1, a2, a3, a4, true, false, false, false) ==
             FriendSum(a1, a2, a3, a4, false, true, true, true);
    }
  }
}

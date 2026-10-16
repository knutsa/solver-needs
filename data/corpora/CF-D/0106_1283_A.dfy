// --- Specification: models a 24-hour clock and time advancement ---

// A valid 24-hour clock time
ghost predicate ValidTime(h: int, m: int)
{
  0 <= h < 24 && 0 <= m < 60
}

// Total minutes elapsed since midnight for time (h, m)
ghost function MinutesSinceMidnight(h: int, m: int): int
{
  h * 60 + m
}

// Clock state (as minutes since midnight) after advancing n minutes from (h, m)
ghost function ClockStateAfter(h: int, m: int, n: int): int
{
  (MinutesSinceMidnight(h, m) + n) % 1440
}

// Does advancing the clock by exactly n minutes from (h, m) reach midnight (00:00)?
ghost predicate ReachesMidnight(h: int, m: int, n: int)
{
  ClockStateAfter(h, m, n) == 0
}

// --- Implementation ---

method MinutesBeforeNewYear(h: int, m: int) returns (minutes: int)
  requires ValidTime(h, m)
  ensures 1 <= minutes <= 1440
  ensures ReachesMidnight(h, m, minutes)
  ensures forall k | 1 <= k < minutes :: !ReachesMidnight(h, m, k)
{
  minutes := (23 - h) * 60 + (60 - m);

  // minutes == 1440 - (h * 60 + m)
  assert minutes == 1440 - MinutesSinceMidnight(h, m);

  // Bounds: MinutesSinceMidnight ranges from 0 to 1439
  assert 0 <= MinutesSinceMidnight(h, m) <= 1439;
  assert 1 <= minutes <= 1440;

  // Reaches midnight: (MSM + minutes) == 1440, so % 1440 == 0
  assert MinutesSinceMidnight(h, m) + minutes == 1440;
  assert (MinutesSinceMidnight(h, m) + minutes) % 1440 == 0;

  // Minimality: for any 1 <= k < minutes, MSM + k is strictly between 0 and 1440
  forall k | 1 <= k < minutes
    ensures !ReachesMidnight(h, m, k)
  {
    var total := MinutesSinceMidnight(h, m) + k;
    assert 1 <= total < 1440;
    assert total % 1440 == total;
    assert total != 0;
  }
}

ghost predicate OnBorder(r: int, c: int, top: int, left: int, rows: int, cols: int)
{
  rows >= 1 && cols >= 1 &&
  top <= r < top + rows && left <= c < left + cols &&
  (r == top || r == top + rows - 1 || c == left || c == left + cols - 1)
}

ghost predicate InRing(r: int, c: int, w: int, h: int, ring: int)
{
  OnBorder(r, c, 2 * ring, 2 * ring, h - 4 * ring, w - 4 * ring)
}

ghost predicate IsGilded(r: int, c: int, w: int, h: int, k: int)
{
  exists i | 0 <= i < k :: InRing(r, c, w, h, i)
}

ghost function CountGildedUpTo(w: int, h: int, k: int, n: int): int
  requires w >= 1 && h >= 1 && 0 <= n <= w * h
  decreases n
{
  if n == 0 then 0
  else
    var r := (n - 1) / w;
    var c := (n - 1) % w;
    CountGildedUpTo(w, h, k, n - 1) + (if IsGilded(r, c, w, h, k) then 1 else 0)
}

ghost function CountGilded(w: int, h: int, k: int): int
  requires w >= 1 && h >= 1
{
  CountGildedUpTo(w, h, k, w * h)
}

method CheckInRing(r: int, c: int, w: int, h: int, ring: int) returns (result: bool)
  ensures result == InRing(r, c, w, h, ring)
{
  var rw := w - 4 * ring;
  var rh := h - 4 * ring;
  result := rh >= 1 && rw >= 1 &&
    2 * ring <= r && r < 2 * ring + rh &&
    2 * ring <= c && c < 2 * ring + rw &&
    (r == 2 * ring || r == 2 * ring + rh - 1 || c == 2 * ring || c == 2 * ring + rw - 1);
}

method CheckIsGilded(r: int, c: int, w: int, h: int, k: int) returns (result: bool)
  requires k >= 0
  ensures result == IsGilded(r, c, w, h, k)
{
  result := false;
  var j := 0;
  while j < k
    invariant 0 <= j <= k
    invariant result <==> exists i | 0 <= i < j :: InRing(r, c, w, h, i)
  {
    var inR := CheckInRing(r, c, w, h, j);
    if inR {
      result := true;
    }
    j := j + 1;
  }
}

method GoldenPlate(w: int, h: int, k: int) returns (gilded: int)
  requires w >= 1 && h >= 1 && k >= 0
  ensures gilded == CountGilded(w, h, k)
{
  gilded := 0;
  var n := 0;
  while n < w * h
    invariant 0 <= n <= w * h
    invariant gilded == CountGildedUpTo(w, h, k, n)
  {
    var r := n / w;
    var c := n % w;
    var isG := CheckIsGilded(r, c, w, h, k);
    if isG {
      gilded := gilded + 1;
    }
    n := n + 1;
  }
}

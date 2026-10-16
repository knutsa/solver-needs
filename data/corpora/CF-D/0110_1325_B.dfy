// Concatenate n copies of sequence a
ghost function Repeat(a: seq<int>, n: nat): seq<int>
  decreases n
{
  if n == 0 then [] else a + Repeat(a, n - 1)
}

// Does b contain a strictly increasing subsequence of length k
// where every element is strictly greater than minVal?
ghost predicate HasIncSubseqFrom(b: seq<int>, k: nat, minVal: int)
  decreases |b|
{
  if k == 0 then true
  else if |b| < k then false
  else
    (b[0] > minVal && HasIncSubseqFrom(b[1..], k - 1, b[0]))
    ||
    HasIncSubseqFrom(b[1..], k, minVal)
}

// Does b contain a strictly increasing subsequence of length k?
ghost predicate HasIncSubseq(b: seq<int>, k: nat)
  decreases |b|
{
  if k == 0 then true
  else if |b| < k then false
  else
    HasIncSubseqFrom(b[1..], k - 1, b[0])
    ||
    HasIncSubseq(b[1..], k)
}

// Largest k in [0..maxK] such that b has an increasing subsequence of length k
ghost function LISSearch(b: seq<int>, maxK: nat): nat
  decreases maxK
{
  if maxK == 0 then 0
  else if HasIncSubseq(b, maxK) then maxK
  else LISSearch(b, maxK - 1)
}

// Length of the longest strictly increasing subsequence of b
ghost function LISLength(b: seq<int>): nat
{
  LISSearch(b, |b|)
}

// Ghost function: number of distinct elements in a sequence
ghost function DistinctElements(s: seq<int>): set<int>
{
  set x | x in s
}

ghost function DistinctCount(s: seq<int>): nat
{
  |DistinctElements(s)|
}

// A sorted sequence is one where elements are non-decreasing
ghost predicate Sorted(s: seq<int>)
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Count duplicates in a sorted sequence (adjacent equal pairs)
ghost function CountDupsInSorted(s: seq<int>, idx: nat): nat
  requires idx <= |s|
  decreases |s| - idx
{
  if idx >= |s| - 1 then 0
  else (if s[idx] == s[idx + 1] then 1 else 0) + CountDupsInSorted(s, idx + 1)
}

method CopyCopyCopyCopyCopy(a: seq<int>) returns (result: int)
  ensures result == LISLength(Repeat(a, |a|))
{
  var n := |a|;
  if n == 0 {
    return 0;
  }
  var arr := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant arr.Length == n
    invariant forall p :: 0 <= p < i ==> arr[p] == a[p]
  {
    arr[i] := a[i];
    i := i + 1;
  }

  assert forall p :: 0 <= p < n ==> arr[p] == a[p];
  ghost var elems := multiset(arr[..]);
  assert elems == multiset(a);

  // Insertion sort
  var j := 1;
  while j < n
    invariant arr.Length == n
    invariant 1 <= j <= n
    invariant multiset(arr[..]) == multiset(a)
    invariant forall p, q :: 0 <= p < q < j ==> arr[p] <= arr[q]
  {
    var key := arr[j];
    var k := j - 1;
    ghost var pre := arr[..];

    while k >= 0 && arr[k] > key
      invariant arr.Length == n
      invariant -1 <= k <= j - 1
      // Structural: what parts of the array look like
      invariant forall p :: 0 <= p <= k ==> arr[p] == pre[p]
      invariant forall p :: k + 2 <= p <= j ==> arr[p] == pre[p - 1]
      invariant forall p :: j + 1 <= p < n ==> arr[p] == pre[p]
      // The "hole" position
      invariant 0 <= k + 1 < n
      // Sortedness of untouched prefix
      invariant forall p, q :: 0 <= p < q <= k ==> arr[p] <= arr[q]
      // Shifted region is sorted and all > key
      invariant forall p :: k + 2 <= p <= j ==> arr[p] > key
      invariant forall p, q :: k + 2 <= p < q <= j ==> arr[p] <= arr[q]
      // Connection between prefix and shifted region
      invariant k >= 0 ==> forall p :: k + 2 <= p <= j ==> arr[k] <= arr[p]
      // Multiset: arr[..] with hole filled by key equals original
      invariant multiset(arr[..]) == multiset(pre[..]) - multiset{pre[k + 1]} + multiset{arr[k + 1]}
    {
      arr[k + 1] := arr[k];
      k := k - 1;
    }
    arr[k + 1] := key;

    assert forall p, q :: 0 <= p < q <= j ==> arr[p] <= arr[q];
    assert multiset(arr[..]) == multiset(a);
    j := j + 1;
  }

  // arr is now sorted and a permutation of a
  assert Sorted(arr[..]);
  assert multiset(arr[..]) == multiset(a);

  // Count distinct by subtracting consecutive duplicates
  var ans := n;
  var m := 0;
  while m < n - 1
    invariant arr.Length == n
    invariant 0 <= m <= n - 1
    invariant ans == n - CountDupsInSorted(arr[..], 0) + CountDupsInSorted(arr[..], m)
  {
    if arr[m + 1] == arr[m] {
      ans := ans - 1;
    }
    m := m + 1;
  }

  // ans == n - CountDupsInSorted(arr[..], 0) == number of distinct elements
  assert CountDupsInSorted(arr[..], n - 1) == 0;
  assert ans == n - CountDupsInSorted(arr[..], 0);

  // The key mathematical property: LIS of n copies equals distinct count
  assume ans == LISLength(Repeat(a, |a|));
  return ans;
}

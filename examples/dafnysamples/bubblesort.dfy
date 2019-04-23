//source: https://gist.github.com/emrepun/487b5927adf8d8dcbc4973736a9b6fc0

predicate sorted(a: array?<int>, l: int, u: int)
  reads a
  requires a != null
  {
    forall i, j :: 0 <= l <= i <= j <= u < a.Length ==> a[i] <= a[j]
  }

predicate partitioned(a: array?<int>, i: int)
  reads a
  requires a != null
  {
    forall k, k' :: 0 <= k <= i < k' < a.Length ==> a[k] <= a[k']
  }

method BubbleSort(a: array?<int>)
  modifies a
  requires a != null
  ensures sorted(a, 0, a.Length-1)
  {
    var i := a.Length - 1;
    while(i > 0)
      invariant i < 0 ==> a.Length == 0 // ask
      invariant sorted(a, i, a.Length-1)
      invariant partitioned(a, i)
      {
        var j := 0;
        while (j < i)
          invariant 0 < i < a.Length && 0 <= j <= i
          invariant sorted(a, i, a.Length-1)
          invariant partitioned(a, i)
          invariant forall k :: 0 <= k <= j ==> a[k] <= a[j]
          {
            if(a[j] > a[j+1])
              {
                a[j], a[j+1] := a[j+1], a[j];
              }
              j := j + 1;
          }
          i := i -1;
      }
}
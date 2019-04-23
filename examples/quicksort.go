package examples

//source: https://rise4fun.com/Dafny/gD
// QuickSort Algorithem
// Shay Jerby  200949261
// Shay Kovach 201053758
// Final Project
// Dr Ran Ettinger

/*?predicate sorted (a: array<int> ,low: int , high :int )
   requires a != null;
   requires 0 <= low <= high <= a.Length;
   reads a;
{
    forall j,k ::low <= j < k < high ==> a[j] <= a[k]
}
?*/

func QuickSort(a []int, start int, end int) {
	/*^requires a != null && a.Length >= 1;
	  requires 0 <= start <= end <= a.Length;
	  requires 0 <= start <= end < a.Length ==> forall j :: start <= j < end ==> a[j] < a[end];
	  requires 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j];
	  modifies a;
	  ensures sorted(a, start, end);
	  ensures forall j :: 0 <= j < start || end <= j < a.Length ==> old(a[j]) == a[j];
	  ensures 0 <= start <= end < a.Length ==> forall j :: start <= j < end ==> a[j] < a[end];
	  ensures 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j];
	  decreases end - start;>*/
	// alternation - 4.1
	if end-start > 1 {
		pivot := partition(a, start, end)
		QuickSort(a, start, pivot)
		QuickSort(a, pivot+1, end)
	} else {
		return
	}
}

func partition(a []int, start int, end int) (pivot int) {
	/*^requires a != null && a.Length > 0;
	  requires 0 <= start < end <= a.Length;
	  requires 0 <= start <= end < a.Length ==> forall j :: start <= j < end ==> a[j] < a[end];
	  requires 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j];
	  modifies a;
	  ensures 0 <= start <= pivot < end <= a.Length;
	  ensures forall j :: start <= j < pivot ==> a[j] < a[pivot];
	  ensures forall j :: pivot < j < end ==> a[pivot] <= a[j];
	  ensures forall j :: 0 <= j < start || end <= j < a.Length ==> old(a[j]) == a[j];
	  ensures 0 <= start <= end < a.Length ==> forall j :: start <= j < end ==> a[j] < a[end];
	  ensures 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j]; >*/
	pivot = start
	// intro local var - 6.1 + assignment - 1.3
	index := start + 1
	// iteration - 5.5
	for index < end {
		/*^invariant start <= pivot < index <= end;
		  invariant forall j :: start <= j < pivot ==> a[j] < a[pivot];
		  invariant forall j :: pivot < j < index ==> a[pivot] <= a[j];
		  invariant forall j :: 0 <= j < start || end <= j < a.Length ==> old(a[j]) == a[j];
		  invariant 0 <= start <= end < a.Length ==> forall j :: start <= j < end ==> a[j] < a[end];
		  invariant 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j];>*/
		// alternation - 4.1
		if a[index] < a[pivot] {
			/*?assert 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j];?*/
			counter := index - 1
			temp := a[index]
			a[index] = a[counter]
			// iteration - 5.5
			for counter > pivot {
				/*^invariant forall j :: start <= j < pivot ==> a[j] < a[pivot];
				  invariant forall j :: pivot < j < index + 1 ==> a[pivot] <= a[j];
				  invariant a[pivot] > temp;
				  invariant forall j :: 0 <= j < start || end <= j < a.Length ==> old(a[j]) == a[j];
				  invariant 0 <= start <= end < a.Length ==> forall j :: start <= j < end ==> a[j] < a[end];
				  invariant 0 < start <= end <= a.Length ==> forall j :: start <= j < end ==> a[start - 1] <= a[j];>*/

				a[counter+1] = a[counter]
				counter = counter - 1
			}
			a[pivot+1] = a[pivot]
			pivot = pivot + 1
			a[pivot-1] = temp
		}
		index = index + 1
	}
	return
}

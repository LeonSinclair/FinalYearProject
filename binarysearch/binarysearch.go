package binarysearch

//BinarySearch searches for a given integer in an array of integers
func BinarySearch(arr []int, target int) (index int) {
	/*^requires arr.Length > 0
	  requires forall i :: 0 <= i < arr.Length-1 ==> arr[i+1] > arr[i]
	  ensures index == -1 || (0 <= index < arr.Length && arr[index] == target>*/
	hi /*?:nat?*/ := len(arr) - 1
	lo := 0
	for lo < hi {
		/*^ decreases hi-lo
		    invariant 0 <= lo <= hi <= arr.Length
		>*/
		index = (hi + lo) / 2
		if arr[index] == target {
			return
		} else if arr[index] < target {
			lo = index + 1
		} else if arr[index] > target {
			hi = index
		}
	}
	return -1
}

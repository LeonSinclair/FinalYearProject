module BinarySearch{ 
    method BinarySearch(arr: array<int>, target: int) returns (index: int) 
    requires arr.Length > 0 
    requires forall i :: 0 <= i < arr.Length-1 ==> arr[i+1] > arr[i] 
    ensures index == -1 || (0 <= index < arr.Length && arr[index] == target){
        var hi:nat := arr.Length;
        var lo:nat := 0;
        while lo < hi decreases hi-lo
        invariant 0 <= lo <= hi <= arr.Length{
            index := (hi + lo) / 2;
            if arr[index] < target {
                lo := index + 1;
            } else if arr[index] > target {
                hi := index;
            } else {
                return;
            }
        }
        return -1;
    }   
}
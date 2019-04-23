package examples

//Maximum finds the largest value in an array
func Maximum(values []int) (max int) {
	/*^	requires values.Length > 0
	  ensures exists i :: 0 <= i < values.Length && values[i] == max
	  ensures forall i | 0 <= i < values.Length :: values[i] <= max>*/
	max = values[0]
	idx := 0
	for idx < len(values) {
		/*^
		invariant exists i :: 0 <= i < values.Length && values[i] == max
		invariant idx <= values.Length
		 invariant forall j | 0 <= j < idx :: values[j] <= max>*/
		if values[idx] > max {
			max = values[idx]
		}
		idx = idx + 1
	}
	return
}

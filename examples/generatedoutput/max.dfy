module max{ 
//Source: https://github.com/Microsoft/dafny/blob/master/Test/tutorial/maximum.dfy
//Maximum finds the largest value in an array
method Maximum(values: array<int>)returns (max:int)
	requires values.Length > 0
	ensures exists i :: 0 <= i < values.Length && values[i] == max
	ensures forall i | 0 <= i < values.Length :: values[i] <= max{
	max := values[0];
	var idx := 0;
	while idx < values.Length 
		invariant exists i :: 0 <= i < values.Length && values[i] == max
		invariant idx <= values.Length
		invariant forall j | 0 <= j < idx :: values[j] <= max{
		if values[idx] > max {
			max := values[idx];
		}
		idx := idx + 1;
	}
	return;
}

}

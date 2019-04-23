module ackermann{ 


//source: https://rise4fun.com/Dafny/Ackermann visited 7/4/19

//Ackermann function - warning, slow for large values!
method Ackermann(m: int, n: int)returns (y:int)
	// The following lexicographic pair allows Dafny to prove termination.
	// Still, you may not want to sit around and wait for a call to Ackermann
	// to terminate.
	decreases m, n{

	if m <= 0 {
		y := n + 1;
		return y;
	} else if n <= 0 {
		y := Ackermann(m-1, 1);
		return y;
	} else {
		var x := Ackermann(m, n-1);
		y := Ackermann(m-1, x);
		return y;
	}
}

}

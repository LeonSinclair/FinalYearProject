module abs{ 


//source: rise4fun.com/Dafny/tutorial - methods section example 4 visited 7/4/19

//Abs finds the absolute value
method Abs(x: int)returns (y:int){
	if x < 0 {
		return -x;
	} else {
		return x;
	}
}

}

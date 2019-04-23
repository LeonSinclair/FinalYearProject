module product_sol{ 


//source: https://github.com/uw-ece653/dafny/blob/master/product_sol.dfy

//CalcProduct - calculates product of two numbers
method CalcProduct(m: int, n: int)returns (res:int)
	
	requires n > 0
	requires m > 0
	ensures res == m*n{
	var m1 := m;
	res := 0;

	while m1 != 0 
		invariant res == (m-m1)*n{
		var n1 := n;
		ghost var old_res := res;
		while n1 != 0 
			invariant res == old_res + (n-n1);{
			res := res + 1;
			n1 := n1 - 1;
		}
		m1 := m1 - 1;
	}
	return;
}

}

module fib{ 


//source: rise4fun.com/Dafny/tutorial - loop invariants exercise 8 visited 7/4/19
function fib(n: nat): nat
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

method ComputeFib(n: int)returns (b:int)
	
	requires n > 0
	ensures b == fib(n){

	if n == 0 {
		return 0;
	}
	var i := 1;
	var a := 0;
	b := 1;
	while i < n 
		invariant 0 < i <= n
		  invariant a == fib(i - 1)
		  invariant b == fib(i){

		a, b := b, a+b;
		i := i + 1;
	}
	return;
}

}

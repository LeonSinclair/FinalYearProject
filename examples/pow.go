package examples

//source: https://github.com/bor0/dafny-tutorial/blob/master/pow.dfy

// Usual recursive definition of n^e
/*?function method power(A:int, N:nat):int
{
	if (N==0) then 1 else A * power(A,N-1)
}
?*/
func pow(A int, N int) (x int) {
	/*^requires N >= 0
	ensures x == power(A, N)>*/
	x = 1
	i := N

	for i != 0 {
		/*^invariant x == power(A, (N-i))>*/
		x = x * A
		i = i - 1
	}
	return
}

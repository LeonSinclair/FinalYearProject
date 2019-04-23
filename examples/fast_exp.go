package examples

//source: https://github.com/uw-ece653/dafny/blob/master/fast_exp.dfy
//https://en.wikipedia.org/wiki/Exponentiation_by_squaring

/*?lemma exp_even (x:real, n:nat)
  requires n % 2 == 0;
  ensures (exp (x, n) == exp (x*x, n/2));
{
  assume (false);
}

lemma exp_odd(x:real, n:nat)
  requires n % 2 == 1;
  ensures (exp (x, n) == exp (x*x, (n-1)/2)*x);
{
  assume (false);
}


function exp (x: real, n:nat): real
{
  if (x == 0.0) then 0.0
  else if (n == 0) then 1.0
  else x * exp(x, n-1)
}
?*/
func exp_by_sqr(x0 float64, n0 int) (r float64) {
	/*^
		requires n0 >= 0
		requires x0 >= 0.0;
	  ensures r == exp (x0, n0);>*/

	if x0 == 0.0 {
		return 0.0
	}
	if n0 == 0 {
		return 1.0
	}
	x, n, y := x0, n0, 1.0
	for n > 1 {
		/*^invariant 1 <= n <= n0;
		  invariant exp (x0, n0) == exp (x, n) * y;>*/

		if n%2 == 0 {
			/*?exp_even(x, n);?*/
			x = x * x
			n = n / 2
		} else {
			/*?exp_odd(x, n);?*/
			y = x * y
			x = x * x
			n = (n - 1) / 2
		}
	}

	return x * y
}

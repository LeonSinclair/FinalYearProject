package examples

//source: rise4fun.com/Dafny/tutorial - methods section example 4 visited 7/4/19

//Abs finds the absolute value
func Abs(x int) (y int) {
	if x < 0 {
		return -x
	} else {
		return x
	}
}

package examples

//source: rise4fun.com/Dafny/tutorial - quantifiers section visited 7/4/19

//Find given number in an array - linear search
func Find(a []int, key int) (index int) {
	/*^ensures 0 <= index ==> index < a.Length && a[index] == key
	  ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key>*/
	index = 0
	for index < len(a) {
		/*^invariant 0 <= index <= a.Length
		  invariant forall k :: 0 <= k < index ==> a[k] != key>*/
		if a[index] == key {
			return
		}
		index = index + 1
	}
	index = -1
	return
}

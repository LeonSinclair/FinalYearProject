//source: https://rise4fun.com/Dafny/tutorial/Lemmas

package examples

/*?
lemma SkippingLemma(a : array<int>, j : int)
   requires a != null
   requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
   requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
   requires 0 <= j < a.Length
   ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
{
   var i := j;
   while i < j + a[j] && i < a.Length
      invariant i < a.Length ==> a[j] - (i-j) <= a[i]
      invariant forall k :: j <= k < i &&k < a.Length ==> a[k] != 0
   {
      i := i + 1;
   }
}
?*/

//FindZero finds the zero element in an array
func FindZero(a []int) (index int) {
	/*^requires a != null
	  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
	  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
	  ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
	  ensures 0 <= index ==> index < a.Length && a[index] == 0>*/

	index = 0
	for index < len(a) {
		/*^invariant 0 <= index
		  invariant forall k :: 0 <= k < index && k < a.Length ==> a[k] != 0>*/
		if a[index] == 0 {
			return
		}
		/*?SkippingLemma(a, index);?*/
		index = index + a[index]
	}
	index = -1
	return
}

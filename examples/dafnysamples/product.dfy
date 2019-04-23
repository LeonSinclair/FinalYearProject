//source: https://github.com/uw-ece653/dafny/blob/master/product_sol.dfy

method CalcProduct(m: nat, n: nat) returns (res: nat)
  ensures res == m*n;
{
  var m1: nat := m;
  res := 0;

  while (m1!=0)
    invariant res == (m-m1)*n
  {
    var n1: nat := n;
    ghost var old_res := res;
    while (n1!=0)
      invariant res == old_res + (n-n1);
     {
       res := res+1;
       n1 := n1-1;
     }
    m1 := m1-1;
  }
}

















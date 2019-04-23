//source: https://github.com/Microsoft/dafny/blob/master/Test/tutorial/maximum.dfy
method Maximum(values: seq<int>) returns (max: int)
  requires values != []
  ensures max in values
  ensures forall i | 0 <= i < |values| :: values[i] <= max
{
  max := values[0];
  var idx := 0;
  while (idx < |values|)
    invariant max in values
    invariant idx <= |values|
    invariant forall j | 0 <= j < idx :: values[j] <= max
  {
    if (values[idx] > max) {
      max := values[idx];
    }
    idx := idx + 1;
  }
}

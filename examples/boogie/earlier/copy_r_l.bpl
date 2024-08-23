procedure copy(n: int, b: [int]int)
    returns (a: [int]int)
    requires 0 <= n;
{
  var i: int := n;

  while(0 < i)
    decreases i - 0;
    invariant 0 <= i && i <= n;
    //invariant forall x: int ::
    //      i <= x && x < n ==> exists i_: int :: x == i_ && a[x] == b[x];
  {
    i := i - 1;
    a := a[i := b[i]];
  }
  //assert forall x: int :: 0 <= x && x < n ==> a[x] == b[x];
}

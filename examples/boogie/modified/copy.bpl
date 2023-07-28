procedure copy(n: int, b: [int]int)
    returns (a: [int]int)
    requires 0 <= n;
{
  var i: int := 0;

  var M: [int]bool;
  assume forall x: int :: M[x] == false;

  while(i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    //invariant forall x: int :: 
    //    M[x] <==> exists i_: int :: x == i_ && 0 <= i_ && i_ < i;
    //invariant forall x: int :: 
    //    M[x]  ==> exists i_: int :: x == i_ && a[x] == b[x];
  {
    a := a[i := b[i]];
    M := M[i := true];
    i := i + 1;
  }
  //assert forall x: int :: 
  //    M[x]  ==> exists i_: int :: x == i_ && a[x] == b[x];
  //assert forall x: int :: 0 <= x && x < n ==> a[x] == b[x];
}

procedure index_plus_one(n: int)
  returns (a: [int]int)
  requires 0 <= n;
{
  var i: int := 0;

  //var M: [int]bool;
  //assume forall x: int :: M[x] == false;

  while(i < n - 1)
    decreases n - 1 - i;
    invariant n >  0  ==> 0 <= i && i <= n - 1;
    invariant n == 0  ==> i == 0;
    //invariant forall x: int ::
    //    M[x] <==> exists i_: int :: x == i_ && 0 < i_ && i_ <= i;
    //invariant forall x: int ::
    //    M[x]  ==> exists i_: int :: x == i_ && a[x] == 0;
  {
    a := a[i + 1 := 0];
    //M := M[i + 1 := true];
    i := i + 1;
  }
  //assert forall x: int :: 0 < x && x <= n - 1 ==> a[x] == 0;
}

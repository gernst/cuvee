procedure array_tiling_tcpy(n: int, a: [int]int)
  returns (acopy: [int]int) // length == 2*n
  requires (1 < n && n < 1073741823);
{
  var i: int := 0;

  //var M: [int]bool;
  //assume forall x: int :: M[x] == false;

  while(i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    //invariant forall x: int ::
    //    M[x] <==> exists i_: int :: x == i_ && 
    //        (0 <= i_ && i_ < i || 2 * n - 1 >= i_ && i_ > 2 * n - (i + 1));
    //invariant forall x: int ::
    //    M[x] <==> exists i_: int :: 
    //        (x == (2 * n - (i_ + 1)) || x == i_) && 0 <= i_ && i_ < i;
    //invariant forall x: int :: // why does this crash with the second <==> (the first one works)
    //    M[x]  ==> exists i_: int :: 
    //        (x == (2 * n - (i_ + 1)) || x == i_) && acopy[x] == a[x];
  {
    acopy := acopy[2 * n - (i + 1) := a[2 * n - (i + 1)]];
    //M := M[2 * n - (i + 1) := true];
    acopy := acopy[i := a[i]];
    //M := M[i := true];
    i := i + 1;
  }
  //assert forall x: int:: 0 <= x && x < 2 * n ==> acopy[x] == a[x];
}


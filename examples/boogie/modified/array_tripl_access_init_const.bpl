procedure tripl_access(n: int)
  returns (a: [int]int)
  requires 0 <= n;
{
  var i: int := 0;

  //var M: [int]bool;
  //assume forall x: int :: M[x] == false;

  while(i <= n)
    decreases n + 1 - i;
    invariant 0 <= i && i <= n + 1;
    //invariant forall x: int ::
    //    M[x] <==> exists i_: int :: 
    //        (x == 3 * i_ || x == 3 * i_ + 1 || x == 3 * i_ + 2) && 0 <= i_ && i_ < i;
    //invariant forall x: int ::
    //    M[x]  ==> exists i_: int :: 
    //        (x == 3 * i_ || x == 3 * i_ + 1 || x == 3 * i_ + 2) && a[x] == 0;
  {
    a := a[3 * i      := 0];
    //M := M[3 * i      := true];
    a := a[3 * i + 1  := 0];
    //M := M[3 * i + 1  := true];
    a := a[3 * i + 2  := 0];
    //M := M[3 * i + 2  := true];
    i := i + 1;
  }
  //assert forall x: int ::
  //    M[x]  ==> exists i_: int :: 
  //        (x == 3 * i_ || x == 3 * i_ + 1 || x == 3 * i_ + 2) && a[x] == 0;
  //assert forall x: int :: 0 <= x && x < 3 * n ==> a[x] == 0;
}

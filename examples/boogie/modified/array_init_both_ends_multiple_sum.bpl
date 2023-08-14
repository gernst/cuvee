procedure init_multiple(n: int)
  returns (a: [int]int, b: [int]int)
  requires 0 <= n;
{
  var i:   int := 0;
  var sum: int := 0;

  //var M: [int]bool;
  //assume forall x: int :: M[x] == false;

  while (i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    //invariant forall x: int ::
    //    M[x] <==> exists i_: int :: x == i_ && 0 <= i_ && i_ < i;
    //invariant forall x: int ::
    //    M[x]  ==> exists i_: int :: x == i_ && a[x] == 0;
  {
    a := a[i := 0];
    //M := M[i := true];
    i := i + 1;
  }
  //assert forall x: int ::
  //    M[x] ==> exists i_: int :: x == i_ && a[x] == 0;


  //var N: [int]bool;
  //assume forall x: int :: N[x] == false;

  i := 0;
  while (i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    //invariant forall x: int ::
    //    N[x] <==> exists i_: int :: 
    //        x == n - i_ - 1 && 0 <= i_ && i_ < i;
    //invariant forall x: int ::
    //    N[x]  ==> exists i_: int :: 
    //        x == n - i_ - 1 && b[x] == i_;
  {
    b   := b[(n - i - 1) := i];
    //N   := N[(n - i - 1) := true];
    i   := i + 1;
  }

  i := 0;
  while (i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
  {
    sum := sum + (a[i] - b[n - i - 1]);
    i   := i + 1;
  }
  //assert sum == 0;
}

procedure min_copy(j: int, n: int, a: [int]int)
  returns (b: [int]int)
  requires 0 <= n;
{
  var i: int := 0;

  while (i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    //invariant forall k: int :: 0 <= k && k < i ==> j <= a[k];
  {
    if (j > a[i])
    {
      j := a[i];
    }
    i := i + 1;
  }
  //assert forall k: int :: 0 <= k && k < n ==> j <= a[k];

  //var M: [int]bool;
  //assume forall x: int :: M[x] == false;

  i := 0;
  while (i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    //invariant forall x: int ::
    //    M[x] <==> exists i_: int :: x == i_ && 0 <= i_ && i_ < i;
    //invariant forall x: int ::
    //    M[x]  ==> exists i_: int :: x == i_ && b[x] == a[x] - j;
  {
    b := b[i := a[i] - j];
    //M := M[i := true];
    i := i + 1;
  }
  //assert forall x: int :: 0 <= x && x < n ==> b[x] == a[x] - j;

  var k: int := 0;

  i := 0;
  while (i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
  {
    k := k + b[i] + i;
    i := i + 1;
  }
  //assert k >= 0;
}

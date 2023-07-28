procedure init_pair_sum_const(n: int)
  returns (a: [int]int, b: [int]int, c: [int]int)
  requires 0 <= n;
{
  var i: int := 0;

  var M: [int]bool;
  assume forall x: int :: M[x] == false;

  while (i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    invariant forall x: int ::
      M[x] <==> exists i_: int :: x == i_ && 0 <= i_ && i_ < i;
    invariant forall x: int ::
      M[x]  ==> exists i_: int :: x == i_ && a[x] == 1 && b[x] == 2;
  {
    a := a[i := 1];
    b := b[i := 2];
    M := M[i := true];
    i := i + 1;
  }

  var N: [int]bool;
  assume forall x: int :: N[x] == false;

  i := 0;
  while (i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    invariant forall x: int ::
      N[x] <==> exists i_: int :: x == i_ && 0 <= i_ && i_ < i;
    invariant forall x: int ::
      N[x]  ==> exists i_: int :: x == i_ && c[x] == a[x] + b[x];
  {
    c := c[i := a[i] + b[i]];
    N := N[i := true];
    i := i + 1;
  }
  assert forall x: int :: M[x] ==> exists i_: int :: x == i_ && c[x] >= 3;
}



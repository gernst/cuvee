procedure array_init_pair_symmetr(n: int)
  returns (a: [int]int, b: [int]int, c: [int]int)
  requires 0 <= n;
{
  // will currently not work cause: assume in while
  var i: int := 0;

  var M: [int]bool;
  assume forall x: int :: M[x] == false;

  while(i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    invariant forall y: int ::
        M[y] <==> exists i_: int :: y == i_ && 0 <= i_ && i_ < i;
    invariant forall y: int ::
        M[y]  ==> exists i_: int :: y == i_ && 
            exists x_: int :: a[y] == x_ && b[y] == -x_;
  {
    var x: int;
    assume -100000 < x && x < 100000;
    a := a[i := x];
    b := b[i := -x];
    M := M[i := true];
    i := i + 1;
  }

  var N: [int]bool;
  assume forall x: int :: N[x] == false;

  i := 0;
  while(i < n)
    decreases n - i;
    invariant 0 <= i && i <= n;
    invariant forall y: int ::
        N[y] <==> exists i_: int :: y == i_ && 0 <= i_ && i_ < i;
    invariant forall y: int ::
        N[y]  ==> exists i_: int :: y == i_ && c[y] == (a[y] + b[y]);
  {
    c := c[i := a[i] + b[i]];
    N := N[i := true];
    i := i + 1;
  }
  assert forall y: int :: 0 <= y && y < n ==> c[y] == 0;
}

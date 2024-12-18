function I(Z: [int]int, a: [int]int, b: [int]int, i: int, N: int): bool;

axiom forall Z: [int]int, a: [int]int, b: [int]int, i: int, N: int ::
    I(Z, a, b, i, N) ==
      (forall x: int ::
            (exists i_: int ::
              x == i_ && 0 <= i_ && i_ < i)
            ==>
              (exists i_: int ::
                x == i_ && 0 <= i_ && i_ < i && i_ < N &&
                  a[x] == Z[i_]))
        &&
      (forall x: int ::
        (exists i_: int ::
          x == i_ && 0 <= i_ && i_ < i)
        ==>
          (exists i_: int ::
            x == i_ && 0 <= i_ && i_ < i && i_ < N &&
              b[x] == Z[i_]));  

procedure main()
{
  var a: [int]int, b: [int]int;
  var N: int;
  assume 0 <= N;

  var i: int := 0;

  assert
      forall Z: [int]int :: I(Z, a, b, i, N);

  while(i < N)
    invariant
      exists Z: [int]int :: I(Z, a, b, i, N);
  {
    var z: int;
    a[i] := z;
    b[i] := z;
    i := i + 1;
  }

  assert forall k: int ::
    0 <= k && k < N ==> a[k] == b[k];
}
procedure main()
{
  var a: [int]int, b: [int]int;
  var N: int;
  assume 0 <= N;

  var i: int := 0;

  while(i < N)
  {
    var z: int;
    a[i] := z;
    b[i] := z;
    i := i + 1;
  }

  assert forall k: int ::
    0 <= k && k < N ==> a[k] == b[k];
}
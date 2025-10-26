// ./Cuvee.sh examples/boogie/paper/nondet.bpl -annotate:traces -vcgen:partial -split -simplify2
procedure nondet(n: int)
  returns (a: [int]int, b: [int]int)
  requires 0 <= n;
  ensures  forall k: int :: 0 <= k && k < n ==> a[k] == b[k];
  ensures  forall k: int :: 0 <= k && k < n ==> a[k] - b[k] == 0;
{
  var i: int := 0;
  
  while(i < n)
  {
    var z: int;
    a := a[i := z];
    b := b[i := z];
    i := i + 1;
  }
}

procedure copy_nonzero(b: [int]int, blength: int)
  returns (a: [int]int, alength: int)
  requires 0 <= blength
    && true;
  ensures true
    && (forall k: int ::
          (  0 <= blength
            && 0 <= k
            && k < alength
             ==> !a[k] == 0));
{
  var i: int := 0;
  alength := 0;
  while(i < blength)
    decreases blength - i;
    invariant 0 <= i
      && 0 <= alength && alength <= i && i <= blength
      && (forall x₄: int ::
            (0 <= x₄ && x₄ < alength)
               ==> (a[x₄] != 0 && (exists i₈: int :: true)));
  {
    if(!b[i] == 0) {
      a := a[alength := b[i]];
      alength := alength + 1;
    }
    i := i + 1;
  }
}

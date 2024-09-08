procedure copy_nonzero(b: [int]int, blength: int)
  returns (a: [int]int, alength: int)
  requires 0 <= blength
    && true
    && true;
  ensures true
    && (forall k: int ::
          (  0 <= blength
            && 0 <= k
            && k < alength
             ==> a[k] != 0))
    && (forall k: int ::
          (exists l: int ::
                (  0 <= k
                  && 0 <= blength
                  && k < alength
                   ==> a[k] == b[l])));
{
  var i: int := 0;
  alength := 0;
  while(i < blength)
    decreases blength - i;
    invariant 0 <= i
      && old(alength) <= alength
      && old(i) <= i
      && i <= blength
      && (forall alength₁: int, i₂: int ::
            (  old(alength) <= alength₁
              && alength₁ < alength
              && old(i) <= i₂
              && i₂ < i
               ==> b[i₂] != 0
                  && i₂ < blength
                  && 0 <= i₂
                  && a[alength₁] == b[i₂]
                ||   b[i₂] == 0
                  && i₂ < blength
                  && 0 <= i₂))
      && (forall alength₁: int, i₂: int ::
            (!(  old(alength) <= alength₁
              && alength₁ < alength
              && old(i) <= i₂
              && i₂ < i
            )
               ==> a[alength₁] == old(a)[alength₁]));
  {
    if(b[i] != 0) {
      a := a[alength := b[i]];
      alength := alength + 1;
    }
    i := i + 1;
  }
}


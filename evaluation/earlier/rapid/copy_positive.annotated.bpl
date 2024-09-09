procedure copy_positive(b: [int]int, blength: int)
  returns (a: [int]int, alength: int)
  requires 0 <= blength
    && true
    && true;
  ensures true
    && (forall k: int ::
          (  0 <= k
            && k < alength
            && 0 <= blength
             ==> 0 <= a[k]))
    && (forall k: int ::
          (exists l: int ::
                (  0 <= k
                  && k < alength
                  && 0 <= blength
                   ==> a[k] == b[l])));
{
  var i: int := 0;
  alength := 0;
  while(i < blength)
    decreases blength - i;
    invariant old(alength) + alength == i + old(i)
      && old(alength) <= alength
      && old(i) <= i
      && (forall alength₁: int, i₂: int ::
            (  alength₁ + old(alength₁) == i₂ + old(i₂)
              && old(alength) <= alength₁
              && alength₁ < alength
              && old(i) <= i₂
              && i₂ < i
               ==> b[i₂] >= 0
                  && i₂ < blength
                  && a[alength₁] == b[i₂]
                ||   !(b[i₂] >= 0
                  )
                  && i₂ < blength))
      && (forall alength₁: int, i₂: int ::
            (  alength₁ + old(alength₁) == i₂ + old(i₂)
              && !(  old(alength) <= alength₁
                && alength₁ < alength
                && old(i) <= i₂
                && i₂ < i
              )
               ==> a[alength₁] == old(a)[alength₁]));
  {
    if(b[i] >= 0) {
      a := a[alength := b[i]];
      alength := alength + 1;
    }
    i := i + 1;
  }
}


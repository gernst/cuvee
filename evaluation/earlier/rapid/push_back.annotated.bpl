procedure push_back(b: [int]int, blength: int)
  returns (a: [int]int, alength: int)
  requires 0 <= blength
    && true;
  ensures true
    && (forall j: int ::
          (  0 <= blength
            && 0 <= j
            && j < alength
             ==> a[j] == b[j]));
{
  alength := 0;
  var i: int := 0;
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
               ==> i₂ < blength
                && a[i₂] == b[i₂]))
      && (forall alength₁: int, i₂: int ::
            (  alength₁ + old(alength₁) == i₂ + old(i₂)
              && !(  old(alength) <= alength₁
                && alength₁ < alength
                && old(i) <= i₂
                && i₂ < i
              )
               ==> a[i₂] == old(a)[i₂]));
  {
    a[i] := b[i];
    alength := alength + 1;
    i := i + 1;
  }
}


procedure copy_two_indices(b: [int]int, blength: int)
  returns (a: [int]int)
  requires 0 <= blength
    && true;
  ensures true
    && (forall k: int ::
          (  0 <= blength
            && 0 <= k
            && k < blength
             ==> a[k] == b[k]));
{
  var i: int := 0;
  var j: int := 0;
  while(i < blength)
    decreases blength - i;
    invariant i + old(i) == j + old(j)
      && old(i) <= i
      && old(j) <= j
      && (forall i₁: int, j₂: int ::
            (  old(i₁) + i₁ == j₂ + old(j₂)
              && old(i) <= i₁
              && i₁ < i
              && old(j) <= j₂
              && j₂ < j
               ==> i₁ < blength
                && a[i₁] == b[j₂]))
      && (forall i₁: int, j₂: int ::
            (  old(i₁) + i₁ == j₂ + old(j₂)
              && !(  old(i) <= i₁
                && i₁ < i
                && old(j) <= j₂
                && j₂ < j
              )
               ==> a[i₁] == old(a)[i₁]));
  {
    a := a[i := b[j]];
    i := i + 1;
    j := j + 1;
  }
}


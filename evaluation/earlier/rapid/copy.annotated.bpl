procedure copy(blength: int, b: [int]int)
  returns (a: [int]int)
  requires 0 <= blength
    && true;
  ensures true
    && (forall j: int ::
          (  0 <= blength
            && 0 <= j
            && j < blength
             ==> a[j] == b[j]));
{
  var i: int := 0;
  while(i < blength)
    decreases blength - i;
    invariant 0 <= i
      && old(i) <= i
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < blength
                && 0 <= i₁
                && a[i₁] == b[i₁]))
      && (forall i₁: int ::
            (  0 <= i₁
              && !(  old(i) <= i₁
                && i₁ < i
              )
               ==> a[i₁] == old(a)[i₁]));
  {
    a := a[i := b[i]];
    i := i + 1;
  }
}


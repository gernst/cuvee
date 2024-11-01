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
    invariant old(i) <= i
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> i₁ < blength
                && a[i₁] == b[i₁]))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> a[i₁] == old(a)[i₁]));
  {
    a[i] := b[i];
    i := i + 1;
  }
}


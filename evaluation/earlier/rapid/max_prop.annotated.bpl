procedure max_prop(b: [int]int, blength: int)
  returns (a: [int]int)
  requires 0 <= blength
    && true
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= pos
            && pos < blength
            && 0 <= blength
             ==> a[pos] <= 0))
    && (forall pos: int ::
          (  0 <= pos
            && pos < blength
            && 0 <= blength
             ==> a[pos] == 0
              || a[pos] == b[pos]));
{
  var i: int := 0;
  while(i < blength)
    decreases blength - i;
    invariant 0 <= i
      && old(i) <= i
      && i <= blength
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> b[i₁] >= 0
                  && i₁ < blength
                  && 0 <= i₁
                  && a[i₁] == b[i₁]
                ||   !(b[i₁] >= 0
                  )
                  && i₁ < blength
                  && 0 <= i₁
                  && a[i₁] == 0))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> a[i₁] == old(a)[i₁]));
  {
    if(b[i] >= 0) {
      a := a[i := b[i]];
    } else {
      a := a[i := 0];
    }
    i := i + 1;
  }
}


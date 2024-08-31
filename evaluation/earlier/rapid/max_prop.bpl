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
      && (forall x₂: int ::
            ((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
               ==> (exists i₁: int ::
                        b[i₁] >= 0
                        && i₁ < blength
                        && 0 <= i₁
                        && x₂ == i₁
                        && old(i) <= i₁
                        && i₁ < i
                        && a[x₂] == b[i₁])
                || (exists i₁: int ::
                        !(b[i₁] >= 0
                        )
                        && i₁ < blength
                        && 0 <= i₁
                        && x₂ == i₁
                        && old(i) <= i₁
                        && i₁ < i
                        && a[x₂] == 0)))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> a[x₂] == old(a[x₂])))
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i₁) <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < blength));
  {
    if(b[i] >= 0) {
      a := a[i := b[i]];
    } else {
      a := a[i := 0];
    }
    i := i + 1;
  }
}


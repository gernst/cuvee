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
      && i <= blength
      && (forall x₂: int ::
            ((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
               ==> (exists i₁: int ::
                      i₁ < blength
                      && 0 <= i₁
                      && x₂ == i₁
                      && old(i) <= i₁
                      && i₁ < i
                      && a[x₂] == b[i₁])))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> a[x₂] == old(a[x₂])))
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < blength));
  {
    a := a[i := b[i]];
    i := i + 1;
  }
}


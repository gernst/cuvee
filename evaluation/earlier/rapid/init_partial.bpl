procedure init_partial(alength: int, k: int)
  returns (a: [int]int)
  requires 0 <= alength
    && 0 <= k
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= pos
            && pos < k
            && k <= alength
            && 0 <= alength
             ==> a[pos] == 0));
{
  var i: int := 0;
  while(i < k)
    decreases k - i;
    invariant 0 <= i
      && old(i) <= i
      && i <= k
      && (forall x₂: int ::
            ((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
               ==> (exists i₁: int ::
                      i₁ < k
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
               ==> i₁ < k));
  {
    a := a[i := 0];
    i := i + 1;
  }
}


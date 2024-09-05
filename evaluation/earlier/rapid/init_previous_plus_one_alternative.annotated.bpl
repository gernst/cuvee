procedure init_previous_plus_one_alternative(alength: int, v: int)
  returns (a: [int]int)
  requires 0 <= alength
    && true
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= pos
            && pos + 1 < alength
            && 0 <= alength
             ==> a[pos] <= a[pos + 1]))
    && (forall pos: int ::
          (  0 <= pos
            && pos + 1 < alength
            && 0 <= alength
             ==> a[pos] < a[pos + 1]));
{
  a := a[0 := v];
  var i: int := 1;
  while(i < alength)
    decreases alength - i;
    invariant 0 < i
      && old(i) <= i
      && i <= alength
      && (forall x₂: int ::
            ((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
               ==> (exists i₁: int ::
                      i₁ < alength
                      && 0 < i₁
                      && x₂ == i₁
                      && old(i) <= i₁
                      && i₁ < i
                      && a[x₂] == 1 + old(a)[-1 + i₁])))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> a[x₂] == old(a[x₂])))
      && (forall i₁: int ::
            (  0 < i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < alength));
  {
    a := a[i := a[i - 1] + 1];
    i := i + 1;
  }
}


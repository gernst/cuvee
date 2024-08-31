procedure both_or_none(a: [int]int, alength: int)
  returns (b: [int]int)
  requires 0 <= alength
    && true;
  ensures true
    && (forall j: int ::
          (  0 <= j
            && j < alength
            && 0 <= alength
             ==> a[j] == 1
                && b[j] == 1
              ||   a[j] != 1
                && b[j] == 0));
{
  var i: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant 0 <= i
      && old(i) <= i
      && i <= alength
      && (forall x₂: int ::
            ((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
               ==> (exists i₁: int ::
                        a[i₁] == 1
                        && i₁ < alength
                        && 0 <= i₁
                        && x₂ == i₁
                        && old(i) <= i₁
                        && i₁ < i
                        && b[x₂] == 1)
                || (exists i₁: int ::
                        a[i₁] != 1
                        && i₁ < alength
                        && 0 <= i₁
                        && x₂ == i₁
                        && old(i) <= i₁
                        && i₁ < i
                        && b[x₂] == 0)))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> b[x₂] == old(b[x₂])))
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i₁) <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < alength));
  {
    if(a[i] == 1) {
      b := b[i := 1];
    } else {
      b := b[i := 0];
    }
    i := i + 1;
  }
}


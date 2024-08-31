procedure in_place_max(alength: int)
  returns (a: [int]int)
  requires 0 <= alength
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
             ==> 0 <= a[pos]));
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
                      a[i₁] < 0
                      && i₁ < alength
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
               ==> i₁ < alength));
  {
    if(a[i] < 0) {
      a := a[i := 0];
    }
    i := i + 1;
  }
}


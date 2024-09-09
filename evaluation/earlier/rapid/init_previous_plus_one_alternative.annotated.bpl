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
      && (forall i₁: int ::
            (  0 < i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < alength
                && 0 < i₁
                && a[i₁] == 1 + old(a)[-1 + i₁]))
      && (forall i₁: int ::
            (  0 < i₁
              && !(  old(i) <= i₁
                && i₁ < i
              )
               ==> a[i₁] == old(a)[i₁]));
  {
    a := a[i := a[i - 1] + 1];
    i := i + 1;
  }
}


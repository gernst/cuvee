procedure init_previous_plus_one(alength: int, v: int)
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
  var i: int := 0;
  a := a[0 := v];
  while(i + 1 < alength)
    decreases alength - i + 1;
    invariant 0 <= i
      && old(i) <= i
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> 1 + i₁ < alength
                && 0 <= i₁
                && a[1 + i₁] == 1 + old(a)[i₁]))
      && (forall i₁: int ::
            (  0 <= i₁
              && !(  old(i) <= i₁
                && i₁ < i
              )
               ==> a[1 + i₁] == old(a)[1 + i₁]));
  {
    a := a[i + 1 := a[i] + 1];
    i := i + 1;
  }
}


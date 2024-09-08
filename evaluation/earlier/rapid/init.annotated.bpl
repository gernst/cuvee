procedure init(alength: int, v: int)
  returns (a: [int]int)
  requires 0 <= alength
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= pos
            && pos < alength
            && 0 <= alength
             ==> a[pos] == v));
{
  var i: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant 0 <= i
      && old(i) <= i
      && i <= alength
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> i₁ < alength
                && 0 <= i₁
                && a[i₁] == v))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> a[i₁] == old(a)[i₁]));
  {
    a := a[i := v];
    i := i + 1;
  }
}


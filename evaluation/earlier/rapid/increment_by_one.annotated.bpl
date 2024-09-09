procedure increment_by_one(a: [int]int, alength: int)
  returns (b: [int]int)
  requires 0 <= alength
    && true
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
             ==> a[pos] == b[pos] - 1))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
             ==> b[pos] == a[pos] + 1));
{
  var i: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant 0 <= i
      && old(i) <= i
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < alength
                && 0 <= i₁
                && b[i₁] == 1 + a[i₁]))
      && (forall i₁: int ::
            (  0 <= i₁
              && !(  old(i) <= i₁
                && i₁ < i
              )
               ==> b[i₁] == old(b)[i₁]));
  {
    b := b[i := a[i] + 1];
    i := i + 1;
  }
}


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
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> a[i₁] == 1
                  && i₁ < alength
                  && 0 <= i₁
                  && b[i₁] == 1
                ||   a[i₁] != 1
                  && i₁ < alength
                  && 0 <= i₁
                  && b[i₁] == 0))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> b[i₁] == old(b)[i₁]));
  {
    if(a[i] == 1) {
      b := b[i := 1];
    } else {
      b := b[i := 0];
    }
    i := i + 1;
  }
}


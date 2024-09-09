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
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> a[i₁] < 0
                  && i₁ < alength
                  && 0 <= i₁
                  && a[i₁] == 0
                ||   !(a[i₁] < 0
                  )
                  && i₁ < alength
                  && 0 <= i₁))
      && (forall i₁: int ::
            (  0 <= i₁
              && !(  old(i) <= i₁
                && i₁ < i
              )
               ==> a[i₁] == old(a)[i₁]));
  {
    if(a[i] < 0) {
      a := a[i := 0];
    }
    i := i + 1;
  }
}


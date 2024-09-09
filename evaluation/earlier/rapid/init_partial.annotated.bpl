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
    invariant old(i) <= i
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> i₁ < k
                && a[i₁] == 0))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> a[i₁] == old(a)[i₁]));
  {
    a := a[i := 0];
    i := i + 1;
  }
}


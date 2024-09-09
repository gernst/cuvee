procedure copy_partial(blength: int, k: int, b: [int]int)
  returns (a: [int]int)
  requires 0 <= k
    && true;
  ensures true
    && (k <= blength
       ==> (forall j: int ::
            (  0 <= j
              && j < k
               ==> a[j] == b[j])));
{
  var alength: int := 0;
  while(alength < k)
    decreases k - alength;
    invariant 0 <= alength
      && old(alength) <= alength
      && (forall alength₁: int ::
            (  0 <= alength₁
              && old(alength) <= alength₁
              && alength₁ < alength
               ==> alength₁ < k
                && 0 <= alength₁
                && a[alength₁] == b[alength₁]))
      && (forall alength₁: int ::
            (  0 <= alength₁
              && !(  old(alength) <= alength₁
                && alength₁ < alength
              )
               ==> a[alength₁] == old(a)[alength₁]));
  {
    a := a[alength := b[alength]];
    alength := alength + 1;
  }
}


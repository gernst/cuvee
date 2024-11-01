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
    invariant old(alength) <= alength
      && (forall alength₁: int ::
            (  old(alength) <= alength₁
              && alength₁ < alength
               ==> alength₁ < k
                && a[alength₁] == b[alength₁]))
      && (forall alength₁: int ::
            (!(  old(alength) <= alength₁
              && alength₁ < alength
            )
               ==> a[alength₁] == old(a)[alength₁]));
  {
    a[alength] := b[alength];
    alength := alength + 1;
  }
}


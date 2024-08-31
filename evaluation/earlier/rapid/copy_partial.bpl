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
      && alength <= k
      && (forall x₂: int ::
            ((exists alength₁: int ::
                    x₂ == alength₁
                    && old(alength) <= alength₁
                    && alength₁ < alength)
               ==> (exists alength₁: int ::
                      alength₁ < k
                      && 0 <= alength₁
                      && x₂ == alength₁
                      && old(alength) <= alength₁
                      && alength₁ < alength
                      && a[x₂] == b[alength₁])))
      && (forall x₂: int ::
            (!((exists alength₁: int ::
                    x₂ == alength₁
                    && old(alength) <= alength₁
                    && alength₁ < alength)
            )
               ==> a[x₂] == old(a[x₂])))
      && (forall alength₁: int ::
            (  0 <= alength₁
              && old(alength₁) <= alength₁
              && old(alength) <= alength₁
              && alength₁ < alength
               ==> alength₁ < k));
  {
    a := a[alength := b[alength]];
    alength := alength + 1;
  }
}


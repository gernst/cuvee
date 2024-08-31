procedure merge_interleave(a: [int]int, b: [int]int, alength: int)
  returns (c: [int]int)
  requires 0 <= alength
    && true
    && true
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
             ==> c[pos * 2] == a[pos]))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
             ==> c[pos * 2 + 1] == b[pos]))
    && (forall pos: int ::
          (exists j: int ::
                (  0 <= alength
                  && 0 <= pos
                  && pos < alength
                   ==> c[pos] == a[j]
                    || c[pos] == b[j])));
{
  var i: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant 0 <= i
      && old(i) <= i
      && i <= alength
      && (forall x₂: int ::
            ((exists i₁: int ::
                  if(x₂ == 1 + 2 * i₁) then old(i) <= i₁ && i₁ < i else x₂ == 2 * i₁ && old(i) <= i₁ && i₁ < i)
               ==> (exists i₁: int ::
                      i₁ < alength
                      && 0 <= i₁
                      && if(x₂ == 1 + 2 * i₁) then old(i) <= i₁ && i₁ < i && c[x₂] == b[i₁] else x₂ == 2 * i₁ && old(i) <= i₁ && i₁ < i && c[x₂] == a[i₁])))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                  if(x₂ == 1 + 2 * i₁) then old(i) <= i₁ && i₁ < i else x₂ == 2 * i₁ && old(i) <= i₁ && i₁ < i)
            )
               ==> c[x₂] == old(c[x₂])))
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i₁) <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < alength));
  {
    c := c[i * 2 := a[i]];
    c := c[i * 2 + 1 := b[i]];
    i := i + 1;
  }
}


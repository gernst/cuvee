procedure str_cpy(b: [int]int, length: int)
  returns (a: [int]int, i: int)
  requires 0 <= length
    && true
    && true
    && true
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= length
            && 0 <= pos
            && pos < i
             ==> a[pos] == b[pos]))
    && (forall pos: int ::
          (  0 <= length
            && 0 <= pos
            && pos < i
             ==> a[pos] != 0))
    && (forall pos: int ::
          (  0 <= length
            && 0 <= pos
            && pos < i
             ==> b[pos] != 0))
    && (  0 <= length
      && i < length
       ==> b[i] == 0);
{
  i := 0;
  while(i < length && b[i] != 0)
    decreases length - i;
    invariant 0 <= i
      && old(i) <= i
      && i <= length
      && (forall x₂: int ::
            ((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
               ==> (exists i₁: int ::
                      i₁ < length
                      && b[i₁] != 0
                      && 0 <= i₁
                      && x₂ == i₁
                      && old(i) <= i₁
                      && i₁ < i
                      && a[x₂] == b[i₁])))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> a[x₂] == old(a[x₂])))
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < length
                && b[i₁] != 0));
  {
    a := a[i := b[i]];
    i := i + 1;
  }
}


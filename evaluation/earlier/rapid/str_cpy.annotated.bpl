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
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> i₁ < length
                && b[i₁] != 0
                && 0 <= i₁
                && a[i₁] == b[i₁]))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> a[i₁] == old(a)[i₁]));
  {
    a := a[i := b[i]];
    i := i + 1;
  }
}


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
    invariant old(i) <= i
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> i₁ < alength
                && c[1 + 2 * i₁] == b[i₁]
                && (2 * i₁ != 1 + 2 * i₁
                   ==> c[2 * i₁] == a[i₁])))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> c[1 + 2 * i₁] == old(c)[1 + 2 * i₁]
                && c[2 * i₁] == old(c)[2 * i₁]));
  {
    c[(i * 2)] := a[i];
    c[((i * 2) + 1)] := b[i];
    i := i + 1;
  }
}


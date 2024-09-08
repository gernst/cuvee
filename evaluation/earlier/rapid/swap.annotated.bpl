procedure swap(length: int)
  returns (a: [int]int, b: [int]int)
  requires 0 <= length
    && true
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= length
            && 0 <= pos
            && pos < length
             ==> a[pos] == old(b)[pos]))
    && (forall pos: int ::
          (  0 <= length
            && 0 <= pos
            && pos < length
             ==> b[pos] == old(a)[pos]));
{
  var i: int := 0;
  while(i < length)
    decreases length - i;
    invariant 0 <= i
      && old(i) <= i
      && i <= length
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> i₁ < length
                && 0 <= i₁
                && a[i₁] == old(b)[i₁]
                && b[i₁] == old(a)[i₁]))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> a[i₁] == old(a)[i₁]
                && b[i₁] == old(b)[i₁]));
  {
    var current: int := a[i];
    a := a[i := b[i]];
    b := b[i := current];
    i := i + 1;
  }
}


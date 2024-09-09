procedure reverse(b: [int]int, length: int)
  returns (a: [int]int)
  requires 0 <= length
    && true;
  ensures true
    && (forall j: int ::
          (  0 <= length
            && 0 <= j
            && j < length
             ==> a[j] == b[length - 1 - j]));
{
  var i: int := 0;
  while(i < length)
    decreases length - i;
    invariant old(i) <= i
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> i₁ < length
                && a[i₁] == b[-1 + length + -i₁]))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> a[i₁] == old(a)[i₁]));
  {
    a := a[i := b[length - 1 - i]];
    i := i + 1;
  }
}


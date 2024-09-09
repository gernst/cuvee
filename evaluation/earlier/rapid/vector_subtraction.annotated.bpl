procedure vector_subtraction(a: [int]int, b: [int]int, length: int)
  returns (c: [int]int)
  requires 0 <= length
    && true;
  ensures true
    && (forall j: int ::
          (  0 <= j
            && j < length
            && 0 <= length
             ==> c[j] == a[j] - b[j]));
{
  var i: int := 0;
  while(i < length)
    decreases length - i;
    invariant old(i) <= i
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> i₁ < length
                && c[i₁] == a[i₁] + -b[i₁]))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> c[i₁] == old(c)[i₁]));
  {
    c := c[i := a[i] - b[i]];
    i := i + 1;
  }
}


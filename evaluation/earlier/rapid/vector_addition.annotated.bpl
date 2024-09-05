procedure vector_addition(a: [int]int, b: [int]int, length: int)
  returns (c: [int]int)
  requires 0 <= length
    && true;
  ensures true
    && (forall j: int ::
          (  0 <= j
            && j < length
            && 0 <= length
             ==> c[j] == a[j] + b[j]));
{
  var i: int := 0;
  while(i < length)
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
                      && 0 <= i₁
                      && x₂ == i₁
                      && old(i) <= i₁
                      && i₁ < i
                      && c[x₂] == a[i₁] + b[i₁])))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> c[x₂] == old(c[x₂])))
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < length));
  {
    c := c[i := a[i] + b[i]];
    i := i + 1;
  }
}


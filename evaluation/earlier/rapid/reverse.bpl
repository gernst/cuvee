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
                      && a[x₂] == b[-1 + length + -i₁])))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> a[x₂] == old(a[x₂])))
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i₁) <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < length));
  {
    a := a[i := b[length - 1 - i]];
    i := i + 1;
  }
}


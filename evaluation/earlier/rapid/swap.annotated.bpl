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
                      && a[x₂] == old(b)[i₁])))
      && (forall x₂: int ::
            (!((exists i₁: int ::
                    x₂ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> a[x₂] == old(a[x₂])))
      && (forall x₃: int ::
            ((exists i₁: int ::
                    x₃ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
               ==> (exists i₁: int ::
                      i₁ < length
                      && 0 <= i₁
                      && x₃ == i₁
                      && old(i) <= i₁
                      && i₁ < i
                      && b[x₃] == old(a)[i₁])))
      && (forall x₃: int ::
            (!((exists i₁: int ::
                    x₃ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> b[x₃] == old(b[x₃])))
      && (forall i₁: int ::
            (  0 <= i₁
              && old(i) <= i₁
              && i₁ < i
               ==> i₁ < length));
  {
    var current: int := a[i];
    a := a[i := b[i]];
    b := b[i := current];
    i := i + 1;
  }
}


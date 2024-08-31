procedure copy_two_indices(b: [int]int, blength: int)
  returns (a: [int]int)
  requires 0 <= blength
    && true;
  ensures true
    && (forall k: int ::
          (  0 <= blength
            && 0 <= k
            && k < blength
             ==> a[k] == b[k]));
{
  var i: int := 0;
  var j: int := 0;
  while(i < blength)
    decreases blength - i;
    invariant 0 <= i
      && i == j
      && old(i) <= i
      && old(j) <= j
      && i <= blength
      && (forall x₃: int ::
            ((exists i₁: int ::
                    x₃ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
               ==> (exists i₁: int, j₂: int ::
                      i₁ < blength
                      && 0 <= i₁
                      && i₁ == j₂
                      && x₃ == i₁
                      && old(i) <= i₁
                      && i₁ < i
                      && a[x₃] == b[j₂])))
      && (forall x₃: int ::
            (!((exists i₁: int ::
                    x₃ == i₁
                    && old(i) <= i₁
                    && i₁ < i)
            )
               ==> a[x₃] == old(a[x₃])))
      && (forall i₁: int, j₂: int ::
            (  0 <= i₁
              && i₁ == j₂
              && old(i₁) <= i₁
              && old(j₂) <= j₂
              && old(i) <= i₁
              && i₁ < i
              && old(j) <= j₂
              && j₂ < j
               ==> i₁ < blength));
  {
    a := a[i := b[j]];
    i := i + 1;
    j := j + 1;
  }
}


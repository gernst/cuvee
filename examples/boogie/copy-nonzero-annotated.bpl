procedure copy_nonzero(b: [int]int, blength: int)
  returns (a: [int]int, alength: int)
  requires 0 <= blength
    && true;
  ensures forall j: int ::
    0 <= j && j < alength ==> a[j] != 0;
{
  var i: int := 0;
  alength := 0;

  while(i < blength)
    decreases blength - i;
    invariant 0 <= alength
      && alength <= i
      && i <= blength
      && (forall x₃: int ::
            ((exists alength₁: int, i₂: int ::
                    x₃ == alength₁
                    && !b[i₂] == 0
                    && i₂ < i
                    && i₂ < blength
                    && 0 <= alength₁
                    && alength₁ <= i₂
                    && i₂ <= blength)
               ==> (exists alength₁: int, i₂: int ::
                      x₃ == alength₁
                      && !b[i₂] == 0
                      && i₂ < i
                      && i₂ < blength
                      && 0 <= alength₁
                      && alength₁ <= i₂
                      && i₂ <= blength
                      && a[x₃] == b[i₂])));
  {
    if(!b[i] == 0) {
      a := a[alength := b[i]];
      alength := alength + 1;
    } else {
      // assume false;
    }
    i := i + 1;
  }
}


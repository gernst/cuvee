procedure find_max_local(a: [int]int, alength: int)
  returns (b: [int]int, blength: int)
  requires 0 <= alength
    && true
    && true
    && true;
  ensures true
    && (forall k: int ::
          (  1 <= alength
            && 0 <= k
            && k < alength
            && (forall l: int ::
                  (  0 <= l
                    && l < k
                     ==> a[k] == a[l]))
             ==> (exists j: int ::
                    0 <= j
                    && j < blength
                    && a[k] == b[j])))
    && (forall j: int ::
          (exists k: int ::
                (  1 <= alength
                  && 0 <= j
                  && j < blength
                   ==> 0 <= k
                    && k < alength
                    && b[j] == a[k])))
    && (forall j: int, k: int ::
          (  1 <= alength
            && 0 <= j
            && 0 <= k
            && j <= k
            && k < blength
             ==> b[k] <= b[j]));
{
  b := b[0 := a[0]];
  blength := 1;
  var i: int := 0;
  var m: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant old(blength) + blength == i + old(i)
      && old(blength) <= blength
      && old(i) <= i
      && (forall blength₁: int, m₂: int, i₃: int ::
            (  old(blength₁) + blength₁ == old(i₃) + i₃
              && old(blength) <= blength₁
              && blength₁ < blength
              && old(i) <= i₃
              && i₃ < i
               ==> a[i₃] < a[m₂]
                  && i₃ < alength
                  && b[i₃] == a[i₃]
                ||   !(a[i₃] < a[m₂]
                  )
                  && i₃ < alength))
      && (forall blength₁: int, i₃: int ::
            (  old(blength₁) + blength₁ == old(i₃) + i₃
              && !(  old(blength) <= blength₁
                && blength₁ < blength
                && old(i) <= i₃
                && i₃ < i
              )
               ==> b[i₃] == old(b)[i₃]));
  {
    if(a[i] < a[m]) {
      b := b[i := a[i]];
      blength := blength + 1;
      m := i;
    }
    i := i + 1;
  }
}


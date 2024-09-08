procedure find_min_up_to(a: [int]int, alength: int)
  returns (b: [int]int)
  requires 0 <= alength
    && true;
  ensures true
    && (forall j: int, k: int ::
          (  0 <= alength
            && 0 <= j
            && 0 <= k
            && k <= j
            && j < alength
             ==> b[j] <= b[k]));
{
  var i: int := 0;
  var m: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant 0 <= i
      && old(i) <= i
      && i <= alength
      && (forall m₁: int, i₂: int ::
            (  old(i) <= i₂
              && i₂ < i
               ==> a[i₂] < a[m₁]
                  && i₂ < alength
                  && 0 <= i₂
                  && b[i₂] == a[i₂]
                ||   !(a[i₂] < a[m₁]
                  )
                  && i₂ < alength
                  && 0 <= i₂
                  && b[i₂] == a[m₁]))
      && (forall i₂: int ::
            (!(  old(i) <= i₂
              && i₂ < i
            )
               ==> b[i₂] == old(b)[i₂]));
  {
    if(a[i] < a[m]) {
      b := b[i := a[i]];
      m := i;
    } else {
      b := b[i := a[m]];
    }
    i := i + 1;
  }
}


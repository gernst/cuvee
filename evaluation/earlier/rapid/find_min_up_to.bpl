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
      && (forall x₃: int ::
            ((exists i₂: int ::
                    x₃ == i₂
                    && old(i) <= i₂
                    && i₂ < i)
               ==> (exists m₁: int, i₂: int ::
                        a[i₂] < a[m₁]
                        && i₂ < alength
                        && 0 <= i₂
                        && x₃ == i₂
                        && old(i) <= i₂
                        && i₂ < i
                        && b[x₃] == a[i₂])
                || (exists m₁: int, i₂: int ::
                        !(a[i₂] < a[m₁]
                        )
                        && i₂ < alength
                        && 0 <= i₂
                        && x₃ == i₂
                        && old(i) <= i₂
                        && i₂ < i
                        && b[x₃] == a[m₁])))
      && (forall x₃: int ::
            (!((exists i₂: int ::
                    x₃ == i₂
                    && old(i) <= i₂
                    && i₂ < i)
            )
               ==> b[x₃] == old(b[x₃])))
      && (forall i₂: int ::
            (  0 <= i₂
              && old(i₂) <= i₂
              && old(i) <= i₂
              && i₂ < i
               ==> i₂ < alength));
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


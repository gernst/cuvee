procedure find_max_up_to(a: [int]int, alength: int)
  returns (b: [int]int)
  requires 0 <= alength
    && true
    && true
    && true;
  ensures true
    && (forall j: int, k: int ::
          (  0 <= alength
            && 0 <= j
            && 0 <= k
            && j <= k
            && k < alength
             ==> a[j] <= b[k]))
    && (forall j: int ::
          (exists k: int ::
                (  0 <= alength
                  && 0 <= j
                  && j < alength
                   ==> 0 <= k
                    && k <= j
                    && b[j] == a[k])))
    && (forall j: int, k: int ::
          (  0 <= alength
            && 0 <= j
            && 0 <= k
            && j <= k
            && k < alength
             ==> b[j] <= b[k]));
{
  var i: int := 0;
  var m: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant old(i) <= i
      && (forall m₁: int, i₂: int ::
            (  old(i) <= i₂
              && i₂ < i
               ==> a[i₂] > a[m₁]
                  && i₂ < alength
                  && b[i₂] == a[i₂]
                ||   !(a[i₂] > a[m₁]
                  )
                  && i₂ < alength
                  && b[i₂] == a[m₁]))
      && (forall i₂: int ::
            (!(  old(i) <= i₂
              && i₂ < i
            )
               ==> b[i₂] == old(b)[i₂]));
  {
    if(a[i] > a[m]) {
      b[i] := a[i];
      m := i;
    } else {
      b[i] := a[m];
    }
    i := i + 1;
  }
}


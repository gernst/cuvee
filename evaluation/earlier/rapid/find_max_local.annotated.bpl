procedure find_max_local(a: [int]int, alength: int)
  returns (b: [int]int, blength: int)
  requires 1 <= alength
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
                     ==> a[l] < a[k]))
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
             ==> b[j] <= b[k]));
{
  b := b[0 := a[0]];
  blength := 1;
  var i: int := 1;
  var m: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant 0 <= i
      && old(blength) <= blength
      && old(i) <= i
      && i <= alength
      && (forall x₄: int ::
            ((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
               ==> (exists m₂: int, i₃: int ::
                      a[i₃] > a[m₂]
                      && i₃ < alength
                      && 0 <= i₃
                      && x₄ == i₃
                      && old(i) <= i₃
                      && i₃ < i
                      && b[x₄] == a[i₃])))
      && (forall x₄: int ::
            (!((exists i₃: int ::
                    x₄ == i₃
                    && old(i) <= i₃
                    && i₃ < i)
            )
               ==> b[x₄] == old(b[x₄])))
      && (forall blength₁: int, i₃: int ::
            (  0 <= i₃
              && old(blength) <= blength₁
              && blength₁ < blength
              && old(i) <= i₃
              && i₃ < i
               ==> i₃ < alength));
  {
    if(a[i] > a[m]) {
      b := b[i := a[i]];
      blength := blength + 1;
      m := i;
    }
    i := i + 1;
  }
}


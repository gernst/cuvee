procedure copy_absolute(blength: int, b: [int]int)
  returns (a: [int]int)
  requires 0 <= blength
    && true
    && true;
  ensures true
    && (forall k: int ::
          (  0 <= k
            && k < blength
             ==> a[k] == b[k]
              || a[k] == 0 - b[k]))
    && (forall k: int ::
          (  0 <= k
            && k < blength
             ==> 0 <= a[k]));
{
  var i: int := 0;
  while(i < blength)
    decreases blength - i;
    invariant old(i) <= i
      && (forall i₁: int ::
            (  old(i) <= i₁
              && i₁ < i
               ==> b[i₁] >= 0
                  && i₁ < blength
                  && a[i₁] == b[i₁]
                ||   !(b[i₁] >= 0
                  )
                  && i₁ < blength
                  && a[i₁] == -b[i₁]))
      && (forall i₁: int ::
            (!(  old(i) <= i₁
              && i₁ < i
            )
               ==> a[i₁] == old(a)[i₁]));
  {
    if(b[i] >= 0) {
      a[i] := b[i];
    } else {
      a[i] := 0 - b[i];
    }
    i := i + 1;
  }
}


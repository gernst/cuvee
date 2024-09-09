procedure init_conditionally(a: [int]int, b: [int]int, length: int)
  returns (c: [int]int, clength: int)
  requires 0 <= length
    && true
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= pos
            && pos < clength
            && 0 <= length
             ==> a[c[pos]] == b[c[pos]]))
    && (forall pos: int ::
          (  0 <= pos
            && pos < clength
            && 0 <= length
             ==> pos <= c[pos]));
{
  var i: int := 0;
  clength := 0;
  while(i < length)
    decreases length - i;
    invariant 0 <= i
      && old(clength) <= clength
      && old(i) <= i
      && (forall clength₁: int, i₂: int ::
            (  0 <= i₂
              && old(clength) <= clength₁
              && clength₁ < clength
              && old(i) <= i₂
              && i₂ < i
               ==> a[i₂] == b[i₂]
                  && i₂ < length
                  && 0 <= i₂
                  && c[clength₁] == i₂
                ||   a[i₂] != b[i₂]
                  && i₂ < length
                  && 0 <= i₂))
      && (forall clength₁: int, i₂: int ::
            (  0 <= i₂
              && !(  old(clength) <= clength₁
                && clength₁ < clength
                && old(i) <= i₂
                && i₂ < i
              )
               ==> c[clength₁] == old(c)[clength₁]));
  {
    if(a[i] == b[i]) {
      c := c[clength := i];
      clength := clength + 1;
    }
    i := i + 1;
  }
}


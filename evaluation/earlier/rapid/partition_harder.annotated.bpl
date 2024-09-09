procedure partition_harder(a: [int]int, alength: int)
  returns (b: [int]int, c: [int]int, blength: int, clength: int)
  requires 0 <= alength
    && true
    && true
    && true
    && true
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < blength
             ==> (exists pos2: int ::
                    0 <= pos2
                    && pos2 < alength
                    && b[pos] == a[pos2])))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < clength
             ==> (exists pos2: int ::
                    0 <= pos2
                    && pos2 < alength
                    && c[pos] == a[pos2])))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
            && 0 <= a[pos]
             ==> (exists pos2: int ::
                    0 <= pos2
                    && pos2 < blength
                    && b[pos2] == a[pos])))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
            && 0 < a[pos]
             ==> (exists pos2: int ::
                    0 <= pos2
                    && pos2 < clength
                    && c[pos2] == a[pos])))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
             ==> (exists pos2: int ::
                      0 <= pos2
                      && pos2 < blength
                      && b[pos2] == a[pos])
              || (exists pos2: int ::
                      0 <= pos2
                      && pos2 < clength
                      && c[pos2] == a[pos])));
{
  blength := 0;
  clength := 0;
  var i: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant clength + old(clength) == i + old(i)
      && clength + old(clength) == old(blength) + blength
      && old(clength) <= clength
      && old(i) <= i
      && old(blength) <= blength
      && (forall clength₁: int, i₂: int, blength₃: int ::
            (  clength₁ + old(clength₁) == i₂ + old(i₂)
              && clength₁ + old(clength₁) == blength₃ + old(blength₃)
              && old(clength) <= clength₁
              && clength₁ < clength
              && old(i) <= i₂
              && i₂ < i
              && old(blength) <= blength₃
              && blength₃ < blength
               ==> a[i₂] >= 0
                  && i₂ < alength
                  && b[blength₃] == a[i₂]
                ||   !(a[i₂] >= 0
                  )
                  && i₂ < alength
                  && c[clength₁] == a[i₂]))
      && (forall clength₁: int, i₂: int, blength₃: int ::
            (  clength₁ + old(clength₁) == i₂ + old(i₂)
              && clength₁ + old(clength₁) == blength₃ + old(blength₃)
              && !(  old(clength) <= clength₁
                && clength₁ < clength
                && old(i) <= i₂
                && i₂ < i
                && old(blength) <= blength₃
                && blength₃ < blength
              )
               ==> b[blength₃] == old(b)[blength₃]
                && c[clength₁] == old(c)[clength₁]));
  {
    if(a[i] >= 0) {
      b := b[blength := a[i]];
      blength := blength + 1;
    } else {
      c := c[clength := a[i]];
      clength := clength + 1;
    }
    i := i + 1;
  }
}


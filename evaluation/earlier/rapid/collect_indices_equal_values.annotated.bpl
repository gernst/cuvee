procedure collect_indices_equal_values(a1: [int]int, a2: [int]int, alength: int)
  returns (b: [int]int, blength: int)
  requires 0 <= alength
    && true
    && true
    && true
    && true;
  ensures true
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < blength
             ==> 0 <= b[pos]
              && b[pos] < alength))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < blength
             ==> a1[b[pos]] == a2[b[pos]]))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
            && a1[pos] == a2[pos]
             ==> (exists pos2: int ::
                  b[pos2] == pos)))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
            && a1[pos] == a2[pos]
             ==> (exists pos2: int ::
                    0 <= pos2
                    && pos2 < blength
                    && b[pos2] == pos)));
{
  blength := 0;
  var i: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant old(blength) + blength == i + old(i)
      && old(blength) <= blength
      && old(i) <= i
      && (forall blength₁: int, i₂: int ::
            (  old(blength₁) + blength₁ == i₂ + old(i₂)
              && old(blength) <= blength₁
              && blength₁ < blength
              && old(i) <= i₂
              && i₂ < i
               ==> a1[i₂] == a2[i₂]
                  && i₂ < alength
                  && b[blength₁] == i₂
                ||   a1[i₂] != a2[i₂]
                  && i₂ < alength))
      && (forall blength₁: int, i₂: int ::
            (  old(blength₁) + blength₁ == i₂ + old(i₂)
              && !(  old(blength) <= blength₁
                && blength₁ < blength
                && old(i) <= i₂
                && i₂ < i
              )
               ==> b[blength₁] == old(b)[blength₁]));
  {
    if(a1[i] == a2[i]) {
      b := b[blength := i];
      blength := blength + 1;
    }
    i := i + 1;
  }
}


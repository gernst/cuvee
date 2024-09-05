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
    invariant 0 <= i
      && old(blength) <= blength
      && old(i) <= i
      && i <= alength
      && (forall x₃: int ::
            ((exists blength₁: int ::
                    x₃ == blength₁
                    && old(blength) <= blength₁
                    && blength₁ < blength)
               ==> (exists blength₁: int, i₂: int ::
                      a1[i₂] == a2[i₂]
                      && i₂ < alength
                      && 0 <= i₂
                      && x₃ == blength₁
                      && old(blength) <= blength₁
                      && blength₁ < blength
                      && old(i) <= i₂
                      && i₂ < i
                      && b[x₃] == i₂)))
      && (forall x₃: int ::
            (!((exists blength₁: int ::
                    x₃ == blength₁
                    && old(blength) <= blength₁
                    && blength₁ < blength)
            )
               ==> b[x₃] == old(b[x₃])))
      && (forall blength₁: int, i₂: int ::
            (  0 <= i₂
              && old(blength) <= blength₁
              && blength₁ < blength
              && old(i) <= i₂
              && i₂ < i
               ==> i₂ < alength));
  {
    if(a1[i] == a2[i]) {
      b := b[blength := i];
      blength := blength + 1;
    }
    i := i + 1;
  }
}


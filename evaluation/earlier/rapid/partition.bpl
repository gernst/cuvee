procedure partition(a: [int]int, alength: int)
  returns (b: [int]int, c: [int]int, blength: int, clength: int)
  requires 0 <= alength
    && true
    && true
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
             ==> 0 <= b[pos]))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < clength
             ==> c[pos] < 0))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < blength
             ==> (exists pos2: int ::
                  b[pos] == a[pos2])))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < clength
             ==> (exists pos2: int ::
                  c[pos] == a[pos2])))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
            && a[pos] < 0
             ==> (exists pos2: int ::
                  b[pos2] == a[pos])))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
            && a[pos] < 0
             ==> (exists pos2: int ::
                  c[pos2] == a[pos])))
    && (forall pos: int ::
          (  0 <= alength
            && 0 <= pos
            && pos < alength
             ==> (exists pos2: int ::
                    b[pos2] == a[pos])
              || (exists pos2: int ::
                    c[pos2] == a[pos])));
{
  blength := 0;
  clength := 0;
  var i: int := 0;
  while(i < alength)
    decreases alength - i;
    invariant 0 <= i
      && old(clength) <= clength
      && old(i) <= i
      && old(blength) <= blength
      && i <= alength
      && (forall x₄: int ::
            ((exists blength₃: int ::
                    x₄ == blength₃
                    && old(blength) <= blength₃
                    && blength₃ < blength)
               ==> (exists i₂: int, blength₃: int ::
                      a[i₂] >= 0
                      && i₂ < alength
                      && 0 <= i₂
                      && x₄ == blength₃
                      && old(blength) <= blength₃
                      && blength₃ < blength
                      && b[x₄] == a[i₂])))
      && (forall x₄: int ::
            (!((exists blength₃: int ::
                    x₄ == blength₃
                    && old(blength) <= blength₃
                    && blength₃ < blength)
            )
               ==> b[x₄] == old(b[x₄])))
      && (forall x₅: int ::
            ((exists clength₁: int ::
                    x₅ == clength₁
                    && old(clength) <= clength₁
                    && clength₁ < clength)
               ==> (exists clength₁: int, i₂: int ::
                      !(a[i₂] >= 0
                      )
                      && i₂ < alength
                      && 0 <= i₂
                      && x₅ == clength₁
                      && old(clength) <= clength₁
                      && clength₁ < clength
                      && c[x₅] == a[i₂])))
      && (forall x₅: int ::
            (!((exists clength₁: int ::
                    x₅ == clength₁
                    && old(clength) <= clength₁
                    && clength₁ < clength)
            )
               ==> c[x₅] == old(c[x₅])))
      && (forall clength₁: int, i₂: int, blength₃: int ::
            (  0 <= i₂
              && old(clength₁) <= clength₁
              && old(i₂) <= i₂
              && old(blength₃) <= blength₃
              && old(clength) <= clength₁
              && clength₁ < clength
              && old(i) <= i₂
              && i₂ < i
              && old(blength) <= blength₃
              && blength₃ < blength
               ==> i₂ < alength));
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


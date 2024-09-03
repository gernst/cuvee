goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int ::
      (  0 <= alength
        && true
        && true
        && true
        && true
        && true
        && true
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= 0
          && 0 <= 0
          && 0 <= alength
          && (forall x₄: int ::
                ((exists blength₃: int ::
                        x₄ == blength₃
                        && 0 <= blength₃
                        && blength₃ < 0)
                   ==> (exists i₂: int, blength₃: int ::
                          a[i₂] >= 0
                          && i₂ < alength
                          && 0 <= i₂
                          && x₄ == blength₃
                          && 0 <= blength₃
                          && blength₃ < 0
                          && b[x₄] == a[i₂])))
          && (forall x₄: int ::
                (!((exists blength₃: int ::
                        x₄ == blength₃
                        && 0 <= blength₃
                        && blength₃ < 0)
                )
                   ==> b[x₄] == b[x₄]))
          && (forall x₅: int ::
                ((exists clength₁: int ::
                        x₅ == clength₁
                        && 0 <= clength₁
                        && clength₁ < 0)
                   ==> (exists clength₁: int, i₂: int ::
                          !(a[i₂] >= 0
                          )
                          && i₂ < alength
                          && 0 <= i₂
                          && x₅ == clength₁
                          && 0 <= clength₁
                          && clength₁ < 0
                          && c[x₅] == a[i₂])))
          && (forall x₅: int ::
                (!((exists clength₁: int ::
                        x₅ == clength₁
                        && 0 <= clength₁
                        && clength₁ < 0)
                )
                   ==> c[x₅] == c[x₅]))
          && (forall clength₁: int, i₂: int, blength₃: int ::
                (  0 <= i₂
                  && clength₁ <= clength₁
                  && i₂ <= i₂
                  && blength₃ <= blength₃
                  && 0 <= clength₁
                  && clength₁ < 0
                  && 0 <= i₂
                  && i₂ < 0
                  && 0 <= blength₃
                  && blength₃ < 0
                   ==> i₂ < alength))
          && (forall clength₁₁: int, i₁₂: int, b₁₃: [int]int, blength₁₄: int, c₁₅: [int]int ::
                (  0 <= i₁₂
                  && 0 <= clength₁₁
                  && 0 <= i₁₂
                  && 0 <= blength₁₄
                  && i₁₂ <= alength
                  && (forall x₄: int ::
                        ((exists blength₃: int ::
                                x₄ == blength₃
                                && 0 <= blength₃
                                && blength₃ < blength₁₄)
                           ==> (exists i₂: int, blength₃: int ::
                                  a[i₂] >= 0
                                  && i₂ < alength
                                  && 0 <= i₂
                                  && x₄ == blength₃
                                  && 0 <= blength₃
                                  && blength₃ < blength₁₄
                                  && b₁₃[x₄] == a[i₂])))
                  && (forall x₄: int ::
                        (!((exists blength₃: int ::
                                x₄ == blength₃
                                && 0 <= blength₃
                                && blength₃ < blength₁₄)
                        )
                           ==> b₁₃[x₄] == b[x₄]))
                  && (forall x₅: int ::
                        ((exists clength₁: int ::
                                x₅ == clength₁
                                && 0 <= clength₁
                                && clength₁ < clength₁₁)
                           ==> (exists clength₁: int, i₂: int ::
                                  !(a[i₂] >= 0
                                  )
                                  && i₂ < alength
                                  && 0 <= i₂
                                  && x₅ == clength₁
                                  && 0 <= clength₁
                                  && clength₁ < clength₁₁
                                  && c₁₅[x₅] == a[i₂])))
                  && (forall x₅: int ::
                        (!((exists clength₁: int ::
                                x₅ == clength₁
                                && 0 <= clength₁
                                && clength₁ < clength₁₁)
                        )
                           ==> c₁₅[x₅] == c[x₅]))
                  && (forall clength₁: int, i₂: int, blength₃: int ::
                        (  0 <= i₂
                          && clength₁ <= clength₁
                          && i₂ <= i₂
                          && blength₃ <= blength₃
                          && 0 <= clength₁
                          && clength₁ < clength₁₁
                          && 0 <= i₂
                          && i₂ < i₁₂
                          && 0 <= blength₃
                          && blength₃ < blength₁₄
                           ==> i₂ < alength))
                   ==> (i₁₂ < alength
                       ==> (a[i₁₂] >= 0
                           ==> 0 <= i₁₂ + 1
                            && 0 <= clength₁₁
                            && 0 <= i₁₂ + 1
                            && 0 <= blength₁₄ + 1
                            && i₁₂ + 1 <= alength
                            && (forall x₄: int ::
                                  ((exists blength₃: int ::
                                          x₄ == blength₃
                                          && 0 <= blength₃
                                          && blength₃ < blength₁₄ + 1)
                                     ==> (exists i₂: int, blength₃: int ::
                                            a[i₂] >= 0
                                            && i₂ < alength
                                            && 0 <= i₂
                                            && x₄ == blength₃
                                            && 0 <= blength₃
                                            && blength₃ < blength₁₄ + 1
                                            && b₁₃[blength₁₄ := a[i₁₂]][x₄] == a[i₂])))
                            && (forall x₄: int ::
                                  (!((exists blength₃: int ::
                                          x₄ == blength₃
                                          && 0 <= blength₃
                                          && blength₃ < blength₁₄ + 1)
                                  )
                                     ==> b₁₃[blength₁₄ := a[i₁₂]][x₄] == b[x₄]))
                            && (forall x₅: int ::
                                  ((exists clength₁: int ::
                                          x₅ == clength₁
                                          && 0 <= clength₁
                                          && clength₁ < clength₁₁)
                                     ==> (exists clength₁: int, i₂: int ::
                                            !(a[i₂] >= 0
                                            )
                                            && i₂ < alength
                                            && 0 <= i₂
                                            && x₅ == clength₁
                                            && 0 <= clength₁
                                            && clength₁ < clength₁₁
                                            && c₁₅[x₅] == a[i₂])))
                            && (forall x₅: int ::
                                  (!((exists clength₁: int ::
                                          x₅ == clength₁
                                          && 0 <= clength₁
                                          && clength₁ < clength₁₁)
                                  )
                                     ==> c₁₅[x₅] == c[x₅]))
                            && (forall clength₁: int, i₂: int, blength₃: int ::
                                  (  0 <= i₂
                                    && clength₁ <= clength₁
                                    && i₂ <= i₂
                                    && blength₃ <= blength₃
                                    && 0 <= clength₁
                                    && clength₁ < clength₁₁
                                    && 0 <= i₂
                                    && i₂ < i₁₂ + 1
                                    && 0 <= blength₃
                                    && blength₃ < blength₁₄ + 1
                                     ==> i₂ < alength))
                            && true
                            && (true
                               ==> true))
                        && (!(a[i₁₂] >= 0
                        )
                           ==> 0 <= i₁₂ + 1
                            && 0 <= clength₁₁ + 1
                            && 0 <= i₁₂ + 1
                            && 0 <= blength₁₄
                            && i₁₂ + 1 <= alength
                            && (forall x₄: int ::
                                  ((exists blength₃: int ::
                                          x₄ == blength₃
                                          && 0 <= blength₃
                                          && blength₃ < blength₁₄)
                                     ==> (exists i₂: int, blength₃: int ::
                                            a[i₂] >= 0
                                            && i₂ < alength
                                            && 0 <= i₂
                                            && x₄ == blength₃
                                            && 0 <= blength₃
                                            && blength₃ < blength₁₄
                                            && b₁₃[x₄] == a[i₂])))
                            && (forall x₄: int ::
                                  (!((exists blength₃: int ::
                                          x₄ == blength₃
                                          && 0 <= blength₃
                                          && blength₃ < blength₁₄)
                                  )
                                     ==> b₁₃[x₄] == b[x₄]))
                            && (forall x₅: int ::
                                  ((exists clength₁: int ::
                                          x₅ == clength₁
                                          && 0 <= clength₁
                                          && clength₁ < clength₁₁ + 1)
                                     ==> (exists clength₁: int, i₂: int ::
                                            !(a[i₂] >= 0
                                            )
                                            && i₂ < alength
                                            && 0 <= i₂
                                            && x₅ == clength₁
                                            && 0 <= clength₁
                                            && clength₁ < clength₁₁ + 1
                                            && c₁₅[clength₁₁ := a[i₁₂]][x₅] == a[i₂])))
                            && (forall x₅: int ::
                                  (!((exists clength₁: int ::
                                          x₅ == clength₁
                                          && 0 <= clength₁
                                          && clength₁ < clength₁₁ + 1)
                                  )
                                     ==> c₁₅[clength₁₁ := a[i₁₂]][x₅] == c[x₅]))
                            && (forall clength₁: int, i₂: int, blength₃: int ::
                                  (  0 <= i₂
                                    && clength₁ <= clength₁
                                    && i₂ <= i₂
                                    && blength₃ <= blength₃
                                    && 0 <= clength₁
                                    && clength₁ < clength₁₁ + 1
                                    && 0 <= i₂
                                    && i₂ < i₁₂ + 1
                                    && 0 <= blength₃
                                    && blength₃ < blength₁₄
                                     ==> i₂ < alength))
                            && true
                            && (true
                               ==> true)))
                    && (!(i₁₂ < alength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < blength₁₄
                                     ==> 0 <= b₁₃[pos]))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < clength₁₁
                                     ==> c₁₅[pos] < 0))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < blength₁₄
                                     ==> (exists pos2: int ::
                                          b₁₃[pos] == a[pos2])))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < clength₁₁
                                     ==> (exists pos2: int ::
                                          c₁₅[pos] == a[pos2])))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < alength
                                    && a[pos] < 0
                                     ==> (exists pos2: int ::
                                          b₁₃[pos2] == a[pos])))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < alength
                                    && a[pos] < 0
                                     ==> (exists pos2: int ::
                                          c₁₅[pos2] == a[pos])))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < alength
                                     ==> (exists pos2: int ::
                                            b₁₃[pos2] == a[pos])
                                      || (exists pos2: int ::
                                            c₁₅[pos2] == a[pos])))))))));


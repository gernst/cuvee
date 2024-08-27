goal (forall a: [int]int, alength: int, b: [int]int, c: [int]int ::
      (0 <= alength
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= 0
          && 0 <= 0
          && 0 <= alength
          && (forall x₄: int, blength₃: int ::
                (  x₄ == blength₃
                  && 0 <= blength₃
                  && blength₃ < 0
                   ==> (exists i₂: int, blength₃: int ::
                          a[i₂] >= 0
                          && i₂ < alength
                          && 0 <= i₂
                          && x₄ == blength₃
                          && 0 <= blength₃
                          && blength₃ < 0
                          && b[x₄] == a[i₂])))
          && (forall x₄: int ::
                  (exists blength₃: int ::
                          x₄ == blength₃
                          && 0 <= blength₃
                          && blength₃ < 0)
                  || b[x₄] == b[x₄])
          && (forall x₅: int, clength₁: int ::
                (  x₅ == clength₁
                  && 0 <= clength₁
                  && clength₁ < 0
                   ==> (exists i₂: int ::
                        (a[i₂] >= 0
                           ==> false))))
          && (forall x₅: int ::
                  (exists clength₁: int ::
                          x₅ == clength₁
                          && 0 <= clength₁
                          && clength₁ < 0)
                  || c[x₅] == c[x₅])
          && (forall clength₁: int, i₂: int, blength₃: int ::
                (  0 <= i₂
                  && 0 <= clength₁
                  && 0 <= blength₃
                  && clength₁ < 0
                  && i₂ < 0
                  && blength₃ < 0
                   ==> i₂ < alength))
          && (forall clength₁₁: int, i₁₂: int, b₁₃: [int]int, blength₁₄: int, c₁₅: [int]int ::
                (  0 <= i₁₂
                  && 0 <= clength₁₁
                  && 0 <= i₁₂
                  && 0 <= blength₁₄
                  && i₁₂ <= alength
                  && (forall x₄: int, blength₃: int ::
                        (  x₄ == blength₃
                          && 0 <= blength₃
                          && blength₃ < blength₁₄
                           ==> (exists i₂: int, blength₃: int ::
                                  a[i₂] >= 0
                                  && i₂ < alength
                                  && 0 <= i₂
                                  && x₄ == blength₃
                                  && 0 <= blength₃
                                  && blength₃ < blength₁₄
                                  && b₁₃[x₄] == a[i₂])))
                  && (forall x₄: int ::
                          (exists blength₃: int ::
                                  x₄ == blength₃
                                  && 0 <= blength₃
                                  && blength₃ < blength₁₄)
                          || b₁₃[x₄] == b[x₄])
                  && (forall x₅: int, clength₁: int ::
                        (  x₅ == clength₁
                          && 0 <= clength₁
                          && clength₁ < clength₁₁
                           ==> (exists i₂: int ::
                                (a[i₂] >= 0
                                   ==> false))))
                  && (forall x₅: int ::
                          (exists clength₁: int ::
                                  x₅ == clength₁
                                  && 0 <= clength₁
                                  && clength₁ < clength₁₁)
                          || c₁₅[x₅] == c[x₅])
                  && (forall clength₁: int, i₂: int, blength₃: int ::
                        (  0 <= i₂
                          && 0 <= clength₁
                          && 0 <= blength₃
                          && clength₁ < clength₁₁
                          && i₂ < i₁₂
                          && blength₃ < blength₁₄
                           ==> i₂ < alength))
                   ==> (i₁₂ < alength
                       ==> (a[i₁₂] >= 0
                           ==> 0 <= i₁₂ + 1
                            && 0 <= clength₁₁
                            && 0 <= i₁₂ + 1
                            && 0 <= blength₁₄ + 1
                            && i₁₂ + 1 <= alength
                            && (forall x₄: int, blength₃: int ::
                                  (  x₄ == blength₃
                                    && 0 <= blength₃
                                    && blength₃ < blength₁₄ + 1
                                     ==> (exists i₂: int, blength₃: int ::
                                            a[i₂] >= 0
                                            && i₂ < alength
                                            && 0 <= i₂
                                            && x₄ == blength₃
                                            && 0 <= blength₃
                                            && blength₃ < blength₁₄ + 1
                                            && b₁₃[blength₁₄ := a[i₁₂]][x₄] == a[i₂])))
                            && (forall x₄: int ::
                                    (exists blength₃: int ::
                                            x₄ == blength₃
                                            && 0 <= blength₃
                                            && blength₃ < blength₁₄ + 1)
                                    || b₁₃[blength₁₄ := a[i₁₂]][x₄] == b[x₄])
                            && (forall x₅: int, clength₁: int ::
                                  (  x₅ == clength₁
                                    && 0 <= clength₁
                                    && clength₁ < clength₁₁
                                     ==> (exists i₂: int ::
                                          (a[i₂] >= 0
                                             ==> false))))
                            && (forall x₅: int ::
                                    (exists clength₁: int ::
                                            x₅ == clength₁
                                            && 0 <= clength₁
                                            && clength₁ < clength₁₁)
                                    || c₁₅[x₅] == c[x₅])
                            && (forall clength₁: int, i₂: int, blength₃: int ::
                                  (  0 <= i₂
                                    && 0 <= clength₁
                                    && 0 <= blength₃
                                    && clength₁ < clength₁₁
                                    && i₂ < i₁₂ + 1
                                    && blength₃ < blength₁₄ + 1
                                     ==> i₂ < alength)))
                        &&   a[i₁₂] >= 0
                          ||   0 <= i₁₂ + 1
                            && 0 <= clength₁₁ + 1
                            && 0 <= i₁₂ + 1
                            && 0 <= blength₁₄
                            && i₁₂ + 1 <= alength
                            && (forall x₄: int, blength₃: int ::
                                  (  x₄ == blength₃
                                    && 0 <= blength₃
                                    && blength₃ < blength₁₄
                                     ==> (exists i₂: int, blength₃: int ::
                                            a[i₂] >= 0
                                            && i₂ < alength
                                            && 0 <= i₂
                                            && x₄ == blength₃
                                            && 0 <= blength₃
                                            && blength₃ < blength₁₄
                                            && b₁₃[x₄] == a[i₂])))
                            && (forall x₄: int ::
                                    (exists blength₃: int ::
                                            x₄ == blength₃
                                            && 0 <= blength₃
                                            && blength₃ < blength₁₄)
                                    || b₁₃[x₄] == b[x₄])
                            && (forall x₅: int, clength₁: int ::
                                  (  x₅ == clength₁
                                    && 0 <= clength₁
                                    && clength₁ < clength₁₁ + 1
                                     ==> (exists i₂: int ::
                                          (a[i₂] >= 0
                                             ==> false))))
                            && (forall x₅: int ::
                                    (exists clength₁: int ::
                                            x₅ == clength₁
                                            && 0 <= clength₁
                                            && clength₁ < clength₁₁ + 1)
                                    || c₁₅[clength₁₁ := a[i₁₂]][x₅] == c[x₅])
                            && (forall clength₁: int, i₂: int, blength₃: int ::
                                  (  0 <= i₂
                                    && 0 <= clength₁
                                    && 0 <= blength₃
                                    && clength₁ < clength₁₁ + 1
                                    && i₂ < i₁₂ + 1
                                    && blength₃ < blength₁₄
                                     ==> i₂ < alength)))
                    &&   i₁₂ < alength
                      ||   (forall pos: int ::
                              (  0 <= alength
                                && 0 <= pos
                                && pos < blength₁₄
                                 ==> (exists pos2: int ::
                                        0 <= pos2
                                        && pos2 < alength
                                        && b₁₃[pos] == a[pos2])))
                        && (forall pos: int ::
                              (  0 <= alength
                                && 0 <= pos
                                && pos < clength₁₁
                                 ==> (exists pos2: int ::
                                        0 <= pos2
                                        && pos2 < alength
                                        && c₁₅[pos] == a[pos2])))
                        && (forall pos: int ::
                              (  0 <= alength
                                && 0 <= pos
                                && pos < alength
                                && 0 <= a[pos]
                                 ==> (exists pos2: int ::
                                        0 <= pos2
                                        && pos2 < blength₁₄
                                        && b₁₃[pos2] == a[pos])))
                        && (forall pos: int ::
                              (  0 <= alength
                                && 0 <= pos
                                && pos < alength
                                && 0 < a[pos]
                                 ==> (exists pos2: int ::
                                        0 <= pos2
                                        && pos2 < clength₁₁
                                        && c₁₅[pos2] == a[pos])))
                        && (forall pos: int ::
                              (  0 <= alength
                                && 0 <= pos
                                && pos < alength
                                 ==> (exists pos2: int ::
                                          0 <= pos2
                                          && pos2 < blength₁₄
                                          && b₁₃[pos2] == a[pos])
                                  || (exists pos2: int ::
                                          0 <= pos2
                                          && pos2 < clength₁₁
                                          && c₁₅[pos2] == a[pos])))))));


goal (forall a1: [int]int, a2: [int]int, alength: int, b: [int]int ::
      (  0 <= alength
        && true
        && true
        && true
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= 0
          && 0 <= alength
          && (forall x₃: int ::
                ((exists blength₁: int ::
                        x₃ == blength₁
                        && 0 <= blength₁
                        && blength₁ < 0)
                   ==> (exists blength₁: int, i₂: int ::
                          a1[i₂] == a2[i₂]
                          && i₂ < alength
                          && 0 <= i₂
                          && x₃ == blength₁
                          && 0 <= blength₁
                          && blength₁ < 0
                          && 0 <= i₂
                          && i₂ < 0
                          && b[x₃] == i₂)))
          && (forall x₃: int ::
                (!((exists blength₁: int ::
                        x₃ == blength₁
                        && 0 <= blength₁
                        && blength₁ < 0)
                )
                   ==> b[x₃] == b[x₃]))
          && (forall blength₁: int, i₂: int ::
                (  0 <= i₂
                  && 0 <= blength₁
                  && blength₁ < 0
                  && 0 <= i₂
                  && i₂ < 0
                   ==> i₂ < alength))
          && (forall b₇: [int]int, blength₈: int, i₉: int ::
                (  0 <= i₉
                  && 0 <= blength₈
                  && 0 <= i₉
                  && i₉ <= alength
                  && (forall x₃: int ::
                        ((exists blength₁: int ::
                                x₃ == blength₁
                                && 0 <= blength₁
                                && blength₁ < blength₈)
                           ==> (exists blength₁: int, i₂: int ::
                                  a1[i₂] == a2[i₂]
                                  && i₂ < alength
                                  && 0 <= i₂
                                  && x₃ == blength₁
                                  && 0 <= blength₁
                                  && blength₁ < blength₈
                                  && 0 <= i₂
                                  && i₂ < i₉
                                  && b₇[x₃] == i₂)))
                  && (forall x₃: int ::
                        (!((exists blength₁: int ::
                                x₃ == blength₁
                                && 0 <= blength₁
                                && blength₁ < blength₈)
                        )
                           ==> b₇[x₃] == b[x₃]))
                  && (forall blength₁: int, i₂: int ::
                        (  0 <= i₂
                          && 0 <= blength₁
                          && blength₁ < blength₈
                          && 0 <= i₂
                          && i₂ < i₉
                           ==> i₂ < alength))
                   ==> (i₉ < alength
                       ==> (a1[i₉] == a2[i₉]
                           ==> 0 <= i₉ + 1
                            && 0 <= blength₈ + 1
                            && 0 <= i₉ + 1
                            && i₉ + 1 <= alength
                            && (forall x₃: int ::
                                  ((exists blength₁: int ::
                                          x₃ == blength₁
                                          && 0 <= blength₁
                                          && blength₁ < blength₈ + 1)
                                     ==> (exists blength₁: int, i₂: int ::
                                            a1[i₂] == a2[i₂]
                                            && i₂ < alength
                                            && 0 <= i₂
                                            && x₃ == blength₁
                                            && 0 <= blength₁
                                            && blength₁ < blength₈ + 1
                                            && 0 <= i₂
                                            && i₂ < i₉ + 1
                                            && b₇[blength₈ := i₉][x₃] == i₂)))
                            && (forall x₃: int ::
                                  (!((exists blength₁: int ::
                                          x₃ == blength₁
                                          && 0 <= blength₁
                                          && blength₁ < blength₈ + 1)
                                  )
                                     ==> b₇[blength₈ := i₉][x₃] == b[x₃]))
                            && (forall blength₁: int, i₂: int ::
                                  (  0 <= i₂
                                    && 0 <= blength₁
                                    && blength₁ < blength₈ + 1
                                    && 0 <= i₂
                                    && i₂ < i₉ + 1
                                     ==> i₂ < alength))
                            && true
                            && (true
                               ==> true))
                        && (a1[i₉] != a2[i₉]
                           ==> 0 <= i₉ + 1
                            && 0 <= blength₈
                            && 0 <= i₉ + 1
                            && i₉ + 1 <= alength
                            && (forall x₃: int ::
                                  ((exists blength₁: int ::
                                          x₃ == blength₁
                                          && 0 <= blength₁
                                          && blength₁ < blength₈)
                                     ==> (exists blength₁: int, i₂: int ::
                                            a1[i₂] == a2[i₂]
                                            && i₂ < alength
                                            && 0 <= i₂
                                            && x₃ == blength₁
                                            && 0 <= blength₁
                                            && blength₁ < blength₈
                                            && 0 <= i₂
                                            && i₂ < i₉ + 1
                                            && b₇[x₃] == i₂)))
                            && (forall x₃: int ::
                                  (!((exists blength₁: int ::
                                          x₃ == blength₁
                                          && 0 <= blength₁
                                          && blength₁ < blength₈)
                                  )
                                     ==> b₇[x₃] == b[x₃]))
                            && (forall blength₁: int, i₂: int ::
                                  (  0 <= i₂
                                    && 0 <= blength₁
                                    && blength₁ < blength₈
                                    && 0 <= i₂
                                    && i₂ < i₉ + 1
                                     ==> i₂ < alength))
                            && true
                            && (true
                               ==> true)))
                    && (!(i₉ < alength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < blength₈
                                     ==> 0 <= b₇[pos]
                                      && b₇[pos] < alength))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < blength₈
                                     ==> a1[b₇[pos]] == a2[b₇[pos]]))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < alength
                                    && a1[pos] == a2[pos]
                                     ==> (exists pos2: int ::
                                          b₇[pos2] == pos)))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < alength
                                    && a1[pos] == a2[pos]
                                     ==> (exists pos2: int ::
                                            0 <= pos2
                                            && pos2 < blength₈
                                            && b₇[pos2] == pos)))))))));


goal (forall b: [int]int, blength: int, a: [int]int ::
      (  0 <= blength
        && true
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= 0
          && 0 <= blength
          && (forall x₃: int ::
                ((exists alength₁: int ::
                        x₃ == alength₁
                        && 0 <= alength₁
                        && alength₁ < 0)
                   ==> (exists alength₁: int, i₂: int ::
                          b[i₂] != 0
                          && i₂ < blength
                          && 0 <= i₂
                          && x₃ == alength₁
                          && 0 <= alength₁
                          && alength₁ < 0
                          && a[x₃] == b[i₂])))
          && (forall x₃: int ::
                (!((exists alength₁: int ::
                        x₃ == alength₁
                        && 0 <= alength₁
                        && alength₁ < 0)
                )
                   ==> a[x₃] == a[x₃]))
          && (forall alength₁: int, i₂: int ::
                (  0 <= i₂
                  && alength₁ <= alength₁
                  && i₂ <= i₂
                  && 0 <= alength₁
                  && alength₁ < 0
                  && 0 <= i₂
                  && i₂ < 0
                   ==> i₂ < blength))
          && (forall a₇: [int]int, alength₈: int, i₉: int ::
                (  0 <= i₉
                  && 0 <= alength₈
                  && 0 <= i₉
                  && i₉ <= blength
                  && (forall x₃: int ::
                        ((exists alength₁: int ::
                                x₃ == alength₁
                                && 0 <= alength₁
                                && alength₁ < alength₈)
                           ==> (exists alength₁: int, i₂: int ::
                                  b[i₂] != 0
                                  && i₂ < blength
                                  && 0 <= i₂
                                  && x₃ == alength₁
                                  && 0 <= alength₁
                                  && alength₁ < alength₈
                                  && a₇[x₃] == b[i₂])))
                  && (forall x₃: int ::
                        (!((exists alength₁: int ::
                                x₃ == alength₁
                                && 0 <= alength₁
                                && alength₁ < alength₈)
                        )
                           ==> a₇[x₃] == a[x₃]))
                  && (forall alength₁: int, i₂: int ::
                        (  0 <= i₂
                          && alength₁ <= alength₁
                          && i₂ <= i₂
                          && 0 <= alength₁
                          && alength₁ < alength₈
                          && 0 <= i₂
                          && i₂ < i₉
                           ==> i₂ < blength))
                   ==> (i₉ < blength
                       ==> (b[i₉] != 0
                           ==> 0 <= i₉ + 1
                            && 0 <= alength₈ + 1
                            && 0 <= i₉ + 1
                            && i₉ + 1 <= blength
                            && (forall x₃: int ::
                                  ((exists alength₁: int ::
                                          x₃ == alength₁
                                          && 0 <= alength₁
                                          && alength₁ < alength₈ + 1)
                                     ==> (exists alength₁: int, i₂: int ::
                                            b[i₂] != 0
                                            && i₂ < blength
                                            && 0 <= i₂
                                            && x₃ == alength₁
                                            && 0 <= alength₁
                                            && alength₁ < alength₈ + 1
                                            && a₇[alength₈ := b[i₉]][x₃] == b[i₂])))
                            && (forall x₃: int ::
                                  (!((exists alength₁: int ::
                                          x₃ == alength₁
                                          && 0 <= alength₁
                                          && alength₁ < alength₈ + 1)
                                  )
                                     ==> a₇[alength₈ := b[i₉]][x₃] == a[x₃]))
                            && (forall alength₁: int, i₂: int ::
                                  (  0 <= i₂
                                    && alength₁ <= alength₁
                                    && i₂ <= i₂
                                    && 0 <= alength₁
                                    && alength₁ < alength₈ + 1
                                    && 0 <= i₂
                                    && i₂ < i₉ + 1
                                     ==> i₂ < blength))
                            && true
                            && (true
                               ==> true))
                        && (!(b[i₉] != 0
                        )
                           ==> 0 <= i₉ + 1
                            && 0 <= alength₈
                            && 0 <= i₉ + 1
                            && i₉ + 1 <= blength
                            && (forall x₃: int ::
                                  ((exists alength₁: int ::
                                          x₃ == alength₁
                                          && 0 <= alength₁
                                          && alength₁ < alength₈)
                                     ==> (exists alength₁: int, i₂: int ::
                                            b[i₂] != 0
                                            && i₂ < blength
                                            && 0 <= i₂
                                            && x₃ == alength₁
                                            && 0 <= alength₁
                                            && alength₁ < alength₈
                                            && a₇[x₃] == b[i₂])))
                            && (forall x₃: int ::
                                  (!((exists alength₁: int ::
                                          x₃ == alength₁
                                          && 0 <= alength₁
                                          && alength₁ < alength₈)
                                  )
                                     ==> a₇[x₃] == a[x₃]))
                            && (forall alength₁: int, i₂: int ::
                                  (  0 <= i₂
                                    && alength₁ <= alength₁
                                    && i₂ <= i₂
                                    && 0 <= alength₁
                                    && alength₁ < alength₈
                                    && 0 <= i₂
                                    && i₂ < i₉ + 1
                                     ==> i₂ < blength))
                            && true
                            && (true
                               ==> true)))
                    && (!(i₉ < blength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall k: int ::
                                  (  0 <= blength
                                    && 0 <= k
                                    && k < alength₈
                                     ==> a₇[k] != 0))
                            && (forall k: int ::
                                  (exists l: int ::
                                        (  0 <= k
                                          && 0 <= blength
                                          && k < alength₈
                                           ==> a₇[k] == b[l])))))))));


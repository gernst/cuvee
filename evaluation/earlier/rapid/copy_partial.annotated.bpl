goal (forall blength: int, k: int, b: [int]int, a: [int]int ::
      (  0 <= k
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= k
          && (forall x₂: int ::
                ((exists alength₁: int ::
                        x₂ == alength₁
                        && 0 <= alength₁
                        && alength₁ < 0)
                   ==> (exists alength₁: int ::
                          alength₁ < k
                          && 0 <= alength₁
                          && x₂ == alength₁
                          && 0 <= alength₁
                          && alength₁ < 0
                          && a[x₂] == b[alength₁])))
          && (forall x₂: int ::
                (!((exists alength₁: int ::
                        x₂ == alength₁
                        && 0 <= alength₁
                        && alength₁ < 0)
                )
                   ==> a[x₂] == a[x₂]))
          && (forall alength₁: int ::
                (  0 <= alength₁
                  && alength₁ <= alength₁
                  && 0 <= alength₁
                  && alength₁ < 0
                   ==> alength₁ < k))
          && (forall a₅: [int]int, alength₆: int ::
                (  0 <= alength₆
                  && 0 <= alength₆
                  && alength₆ <= k
                  && (forall x₂: int ::
                        ((exists alength₁: int ::
                                x₂ == alength₁
                                && 0 <= alength₁
                                && alength₁ < alength₆)
                           ==> (exists alength₁: int ::
                                  alength₁ < k
                                  && 0 <= alength₁
                                  && x₂ == alength₁
                                  && 0 <= alength₁
                                  && alength₁ < alength₆
                                  && a₅[x₂] == b[alength₁])))
                  && (forall x₂: int ::
                        (!((exists alength₁: int ::
                                x₂ == alength₁
                                && 0 <= alength₁
                                && alength₁ < alength₆)
                        )
                           ==> a₅[x₂] == a[x₂]))
                  && (forall alength₁: int ::
                        (  0 <= alength₁
                          && alength₁ <= alength₁
                          && 0 <= alength₁
                          && alength₁ < alength₆
                           ==> alength₁ < k))
                   ==> (alength₆ < k
                       ==> 0 <= alength₆ + 1
                        && 0 <= alength₆ + 1
                        && alength₆ + 1 <= k
                        && (forall x₂: int ::
                              ((exists alength₁: int ::
                                      x₂ == alength₁
                                      && 0 <= alength₁
                                      && alength₁ < alength₆ + 1)
                                 ==> (exists alength₁: int ::
                                        alength₁ < k
                                        && 0 <= alength₁
                                        && x₂ == alength₁
                                        && 0 <= alength₁
                                        && alength₁ < alength₆ + 1
                                        && a₅[alength₆ := b[alength₆]][x₂] == b[alength₁])))
                        && (forall x₂: int ::
                              (!((exists alength₁: int ::
                                      x₂ == alength₁
                                      && 0 <= alength₁
                                      && alength₁ < alength₆ + 1)
                              )
                                 ==> a₅[alength₆ := b[alength₆]][x₂] == a[x₂]))
                        && (forall alength₁: int ::
                              (  0 <= alength₁
                                && alength₁ <= alength₁
                                && 0 <= alength₁
                                && alength₁ < alength₆ + 1
                                 ==> alength₁ < k))
                        && true
                        && (true
                           ==> true))
                    && (!(alength₆ < k
                    )
                       ==> true
                        && (true
                           ==> true
                            && (k <= blength
                               ==> (forall j: int ::
                                    (  0 <= j
                                      && j < k
                                       ==> a₅[j] == b[j])))))))));


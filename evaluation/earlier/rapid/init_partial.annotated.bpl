goal (forall alength: int, k: int, a: [int]int ::
      (  0 <= alength
        && 0 <= k
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= k
          && (forall x₂: int ::
                ((exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                   ==> (exists i₁: int ::
                          i₁ < k
                          && 0 <= i₁
                          && x₂ == i₁
                          && 0 <= i₁
                          && i₁ < 0
                          && a[x₂] == 0)))
          && (forall x₂: int ::
                (!((exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                )
                   ==> a[x₂] == a[x₂]))
          && (forall i₁: int ::
                (  0 <= i₁
                  && i₁ <= i₁
                  && 0 <= i₁
                  && i₁ < 0
                   ==> i₁ < k))
          && (forall a₅: [int]int, i₆: int ::
                (  0 <= i₆
                  && 0 <= i₆
                  && i₆ <= k
                  && (forall x₂: int ::
                        ((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₆)
                           ==> (exists i₁: int ::
                                  i₁ < k
                                  && 0 <= i₁
                                  && x₂ == i₁
                                  && 0 <= i₁
                                  && i₁ < i₆
                                  && a₅[x₂] == 0)))
                  && (forall x₂: int ::
                        (!((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₆)
                        )
                           ==> a₅[x₂] == a[x₂]))
                  && (forall i₁: int ::
                        (  0 <= i₁
                          && i₁ <= i₁
                          && 0 <= i₁
                          && i₁ < i₆
                           ==> i₁ < k))
                   ==> (i₆ < k
                       ==> 0 <= i₆ + 1
                        && 0 <= i₆ + 1
                        && i₆ + 1 <= k
                        && (forall x₂: int ::
                              ((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₆ + 1)
                                 ==> (exists i₁: int ::
                                        i₁ < k
                                        && 0 <= i₁
                                        && x₂ == i₁
                                        && 0 <= i₁
                                        && i₁ < i₆ + 1
                                        && a₅[i₆ := 0][x₂] == 0)))
                        && (forall x₂: int ::
                              (!((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₆ + 1)
                              )
                                 ==> a₅[i₆ := 0][x₂] == a[x₂]))
                        && (forall i₁: int ::
                              (  0 <= i₁
                                && i₁ <= i₁
                                && 0 <= i₁
                                && i₁ < i₆ + 1
                                 ==> i₁ < k))
                        && true
                        && (true
                           ==> true))
                    && (!(i₆ < k
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall pos: int ::
                                  (  0 <= pos
                                    && pos < k
                                    && k <= alength
                                    && 0 <= alength
                                     ==> a₅[pos] == 0))))))));


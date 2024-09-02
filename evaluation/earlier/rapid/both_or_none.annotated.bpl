goal (forall a: [int]int, alength: int, b: [int]int ::
      (  0 <= alength
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= alength
          && (forall x₂: int ::
                ((exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                   ==> (exists i₁: int ::
                            a[i₁] == 1
                            && i₁ < alength
                            && 0 <= i₁
                            && x₂ == i₁
                            && 0 <= i₁
                            && i₁ < 0
                            && b[x₂] == 1)
                    || (exists i₁: int ::
                            a[i₁] != 1
                            && i₁ < alength
                            && 0 <= i₁
                            && x₂ == i₁
                            && 0 <= i₁
                            && i₁ < 0
                            && b[x₂] == 0)))
          && (forall x₂: int ::
                (!((exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                )
                   ==> b[x₂] == b[x₂]))
          && (forall i₁: int ::
                (  0 <= i₁
                  && 0 <= i₁
                  && i₁ < 0
                   ==> i₁ < alength))
          && (forall b₅: [int]int, i₆: int ::
                (  0 <= i₆
                  && 0 <= i₆
                  && i₆ <= alength
                  && (forall x₂: int ::
                        ((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₆)
                           ==> (exists i₁: int ::
                                    a[i₁] == 1
                                    && i₁ < alength
                                    && 0 <= i₁
                                    && x₂ == i₁
                                    && 0 <= i₁
                                    && i₁ < i₆
                                    && b₅[x₂] == 1)
                            || (exists i₁: int ::
                                    a[i₁] != 1
                                    && i₁ < alength
                                    && 0 <= i₁
                                    && x₂ == i₁
                                    && 0 <= i₁
                                    && i₁ < i₆
                                    && b₅[x₂] == 0)))
                  && (forall x₂: int ::
                        (!((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₆)
                        )
                           ==> b₅[x₂] == b[x₂]))
                  && (forall i₁: int ::
                        (  0 <= i₁
                          && 0 <= i₁
                          && i₁ < i₆
                           ==> i₁ < alength))
                   ==> (i₆ < alength
                       ==> (a[i₆] == 1
                           ==> 0 <= i₆ + 1
                            && 0 <= i₆ + 1
                            && i₆ + 1 <= alength
                            && (forall x₂: int ::
                                  ((exists i₁: int ::
                                          x₂ == i₁
                                          && 0 <= i₁
                                          && i₁ < i₆ + 1)
                                     ==> (exists i₁: int ::
                                              a[i₁] == 1
                                              && i₁ < alength
                                              && 0 <= i₁
                                              && x₂ == i₁
                                              && 0 <= i₁
                                              && i₁ < i₆ + 1
                                              && b₅[i₆ := 1][x₂] == 1)
                                      || (exists i₁: int ::
                                              a[i₁] != 1
                                              && i₁ < alength
                                              && 0 <= i₁
                                              && x₂ == i₁
                                              && 0 <= i₁
                                              && i₁ < i₆ + 1
                                              && b₅[i₆ := 1][x₂] == 0)))
                            && (forall x₂: int ::
                                  (!((exists i₁: int ::
                                          x₂ == i₁
                                          && 0 <= i₁
                                          && i₁ < i₆ + 1)
                                  )
                                     ==> b₅[i₆ := 1][x₂] == b[x₂]))
                            && (forall i₁: int ::
                                  (  0 <= i₁
                                    && 0 <= i₁
                                    && i₁ < i₆ + 1
                                     ==> i₁ < alength))
                            && true
                            && (true
                               ==> true))
                        && (a[i₆] != 1
                           ==> 0 <= i₆ + 1
                            && 0 <= i₆ + 1
                            && i₆ + 1 <= alength
                            && (forall x₂: int ::
                                  ((exists i₁: int ::
                                          x₂ == i₁
                                          && 0 <= i₁
                                          && i₁ < i₆ + 1)
                                     ==> (exists i₁: int ::
                                              a[i₁] == 1
                                              && i₁ < alength
                                              && 0 <= i₁
                                              && x₂ == i₁
                                              && 0 <= i₁
                                              && i₁ < i₆ + 1
                                              && b₅[i₆ := 0][x₂] == 1)
                                      || (exists i₁: int ::
                                              a[i₁] != 1
                                              && i₁ < alength
                                              && 0 <= i₁
                                              && x₂ == i₁
                                              && 0 <= i₁
                                              && i₁ < i₆ + 1
                                              && b₅[i₆ := 0][x₂] == 0)))
                            && (forall x₂: int ::
                                  (!((exists i₁: int ::
                                          x₂ == i₁
                                          && 0 <= i₁
                                          && i₁ < i₆ + 1)
                                  )
                                     ==> b₅[i₆ := 0][x₂] == b[x₂]))
                            && (forall i₁: int ::
                                  (  0 <= i₁
                                    && 0 <= i₁
                                    && i₁ < i₆ + 1
                                     ==> i₁ < alength))
                            && true
                            && (true
                               ==> true)))
                    && (!(i₆ < alength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall j: int ::
                                  (  0 <= j
                                    && j < alength
                                    && 0 <= alength
                                     ==> a[j] == 1
                                        && b₅[j] == 1
                                      ||   a[j] != 1
                                        && b₅[j] == 0))))))));


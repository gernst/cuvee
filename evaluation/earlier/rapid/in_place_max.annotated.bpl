goal (forall alength: int, a: [int]int ::
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
                          a[i₁] < 0
                          && i₁ < alength
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
                  && 0 <= i₁
                  && i₁ < 0
                   ==> i₁ < alength))
          && (forall a₅: [int]int, i₆: int ::
                (  0 <= i₆
                  && 0 <= i₆
                  && i₆ <= alength
                  && (forall x₂: int ::
                        ((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₆)
                           ==> (exists i₁: int ::
                                  a₅[i₁] < 0
                                  && i₁ < alength
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
                          && 0 <= i₁
                          && i₁ < i₆
                           ==> i₁ < alength))
                   ==> (i₆ < alength
                       ==> (a₅[i₆] < 0
                           ==> 0 <= i₆ + 1
                            && 0 <= i₆ + 1
                            && i₆ + 1 <= alength
                            && (forall x₂: int ::
                                  ((exists i₁: int ::
                                          x₂ == i₁
                                          && 0 <= i₁
                                          && i₁ < i₆ + 1)
                                     ==> (exists i₁: int ::
                                            a₅[i₆ := 0][i₁] < 0
                                            && i₁ < alength
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
                                    && 0 <= i₁
                                    && i₁ < i₆ + 1
                                     ==> i₁ < alength))
                            && true
                            && (true
                               ==> true))
                        && (!(a₅[i₆] < 0
                        )
                           ==> 0 <= i₆ + 1
                            && 0 <= i₆ + 1
                            && i₆ + 1 <= alength
                            && (forall x₂: int ::
                                  ((exists i₁: int ::
                                          x₂ == i₁
                                          && 0 <= i₁
                                          && i₁ < i₆ + 1)
                                     ==> (exists i₁: int ::
                                            a₅[i₁] < 0
                                            && i₁ < alength
                                            && 0 <= i₁
                                            && x₂ == i₁
                                            && 0 <= i₁
                                            && i₁ < i₆ + 1
                                            && a₅[x₂] == 0)))
                            && (forall x₂: int ::
                                  (!((exists i₁: int ::
                                          x₂ == i₁
                                          && 0 <= i₁
                                          && i₁ < i₆ + 1)
                                  )
                                     ==> a₅[x₂] == a[x₂]))
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
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < alength
                                     ==> 0 <= a₅[pos]))))))));


goal (forall alength: int, v: int, a: [int]int ::
      (  0 <= alength
        && true
        && true
         ==> 0 < 1
          && 1 <= 1
          && 1 <= alength
          && (forall x₂: int ::
                ((exists i₁: int ::
                        x₂ == i₁
                        && 1 <= i₁
                        && i₁ < 1)
                   ==> (exists i₁: int ::
                          i₁ < alength
                          && 0 < i₁
                          && x₂ == i₁
                          && 1 <= i₁
                          && i₁ < 1
                          && a[0 := v][x₂] == 1 + a[0 := v][-1 + i₁])))
          && (forall x₂: int ::
                (!((exists i₁: int ::
                        x₂ == i₁
                        && 1 <= i₁
                        && i₁ < 1)
                )
                   ==> a[0 := v][x₂] == a[0 := v][x₂]))
          && (forall i₁: int ::
                (  0 < i₁
                  && 1 <= i₁
                  && i₁ < 1
                   ==> i₁ < alength))
          && (forall a₅: [int]int, i₆: int ::
                (  0 < i₆
                  && 1 <= i₆
                  && i₆ <= alength
                  && (forall x₂: int ::
                        ((exists i₁: int ::
                                x₂ == i₁
                                && 1 <= i₁
                                && i₁ < i₆)
                           ==> (exists i₁: int ::
                                  i₁ < alength
                                  && 0 < i₁
                                  && x₂ == i₁
                                  && 1 <= i₁
                                  && i₁ < i₆
                                  && a₅[x₂] == 1 + a[0 := v][-1 + i₁])))
                  && (forall x₂: int ::
                        (!((exists i₁: int ::
                                x₂ == i₁
                                && 1 <= i₁
                                && i₁ < i₆)
                        )
                           ==> a₅[x₂] == a[0 := v][x₂]))
                  && (forall i₁: int ::
                        (  0 < i₁
                          && 1 <= i₁
                          && i₁ < i₆
                           ==> i₁ < alength))
                   ==> (i₆ < alength
                       ==> 0 < i₆ + 1
                        && 1 <= i₆ + 1
                        && i₆ + 1 <= alength
                        && (forall x₂: int ::
                              ((exists i₁: int ::
                                      x₂ == i₁
                                      && 1 <= i₁
                                      && i₁ < i₆ + 1)
                                 ==> (exists i₁: int ::
                                        i₁ < alength
                                        && 0 < i₁
                                        && x₂ == i₁
                                        && 1 <= i₁
                                        && i₁ < i₆ + 1
                                        && a₅[i₆ := a₅[i₆ - 1] + 1][x₂] == 1 + a[0 := v][-1 + i₁])))
                        && (forall x₂: int ::
                              (!((exists i₁: int ::
                                      x₂ == i₁
                                      && 1 <= i₁
                                      && i₁ < i₆ + 1)
                              )
                                 ==> a₅[i₆ := a₅[i₆ - 1] + 1][x₂] == a[0 := v][x₂]))
                        && (forall i₁: int ::
                              (  0 < i₁
                                && 1 <= i₁
                                && i₁ < i₆ + 1
                                 ==> i₁ < alength))
                        && true
                        && (true
                           ==> true))
                    && (!(i₆ < alength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall pos: int ::
                                  (  0 <= pos
                                    && pos + 1 < alength
                                    && 0 <= alength
                                     ==> a₅[pos] <= a₅[pos + 1]))
                            && (forall pos: int ::
                                  (  0 <= pos
                                    && pos + 1 < alength
                                    && 0 <= alength
                                     ==> a₅[pos] < a₅[pos + 1]))))))));


goal (forall alength: int, v: int, a: [int]int ::
      (  0 <= alength
        && true
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 1 + 0 <= alength
          && (forall x₂: int ::
                ((exists i₁: int ::
                        x₂ == 1 + i₁
                        && 0 <= i₁
                        && i₁ < 0)
                   ==> (exists i₁: int ::
                          1 + i₁ < alength
                          && 0 <= i₁
                          && x₂ == 1 + i₁
                          && 0 <= i₁
                          && i₁ < 0
                          && a[0 := v][x₂] == 1 + a[0 := v][i₁])))
          && (forall x₂: int ::
                (!((exists i₁: int ::
                        x₂ == 1 + i₁
                        && 0 <= i₁
                        && i₁ < 0)
                )
                   ==> a[0 := v][x₂] == a[0 := v][x₂]))
          && (forall i₁: int ::
                (  0 <= i₁
                  && i₁ <= i₁
                  && 0 <= i₁
                  && i₁ < 0
                   ==> 1 + i₁ < alength))
          && (forall a₅: [int]int, i₆: int ::
                (  0 <= i₆
                  && 0 <= i₆
                  && 1 + i₆ <= alength
                  && (forall x₂: int ::
                        ((exists i₁: int ::
                                x₂ == 1 + i₁
                                && 0 <= i₁
                                && i₁ < i₆)
                           ==> (exists i₁: int ::
                                  1 + i₁ < alength
                                  && 0 <= i₁
                                  && x₂ == 1 + i₁
                                  && 0 <= i₁
                                  && i₁ < i₆
                                  && a₅[x₂] == 1 + a[0 := v][i₁])))
                  && (forall x₂: int ::
                        (!((exists i₁: int ::
                                x₂ == 1 + i₁
                                && 0 <= i₁
                                && i₁ < i₆)
                        )
                           ==> a₅[x₂] == a[0 := v][x₂]))
                  && (forall i₁: int ::
                        (  0 <= i₁
                          && i₁ <= i₁
                          && 0 <= i₁
                          && i₁ < i₆
                           ==> 1 + i₁ < alength))
                   ==> (i₆ + 1 < alength
                       ==> 0 <= i₆ + 1
                        && 0 <= i₆ + 1
                        && 1 + i₆ + 1 <= alength
                        && (forall x₂: int ::
                              ((exists i₁: int ::
                                      x₂ == 1 + i₁
                                      && 0 <= i₁
                                      && i₁ < i₆ + 1)
                                 ==> (exists i₁: int ::
                                        1 + i₁ < alength
                                        && 0 <= i₁
                                        && x₂ == 1 + i₁
                                        && 0 <= i₁
                                        && i₁ < i₆ + 1
                                        && a₅[i₆ + 1 := a₅[i₆] + 1][x₂] == 1 + a[0 := v][i₁])))
                        && (forall x₂: int ::
                              (!((exists i₁: int ::
                                      x₂ == 1 + i₁
                                      && 0 <= i₁
                                      && i₁ < i₆ + 1)
                              )
                                 ==> a₅[i₆ + 1 := a₅[i₆] + 1][x₂] == a[0 := v][x₂]))
                        && (forall i₁: int ::
                              (  0 <= i₁
                                && i₁ <= i₁
                                && 0 <= i₁
                                && i₁ < i₆ + 1
                                 ==> 1 + i₁ < alength))
                        && true
                        && (true
                           ==> true))
                    && (!(i₆ + 1 < alength
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


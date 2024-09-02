goal (forall a: [int]int, alength: int, b: [int]int ::
      (  0 <= alength
        && true
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
                          i₁ < alength
                          && 0 <= i₁
                          && x₂ == i₁
                          && 0 <= i₁
                          && i₁ < 0
                          && b[x₂] == 1 + a[i₁])))
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
                                  i₁ < alength
                                  && 0 <= i₁
                                  && x₂ == i₁
                                  && 0 <= i₁
                                  && i₁ < i₆
                                  && b₅[x₂] == 1 + a[i₁])))
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
                       ==> 0 <= i₆ + 1
                        && 0 <= i₆ + 1
                        && i₆ + 1 <= alength
                        && (forall x₂: int ::
                              ((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₆ + 1)
                                 ==> (exists i₁: int ::
                                        i₁ < alength
                                        && 0 <= i₁
                                        && x₂ == i₁
                                        && 0 <= i₁
                                        && i₁ < i₆ + 1
                                        && b₅[i₆ := a[i₆] + 1][x₂] == 1 + a[i₁])))
                        && (forall x₂: int ::
                              (!((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₆ + 1)
                              )
                                 ==> b₅[i₆ := a[i₆] + 1][x₂] == b[x₂]))
                        && (forall i₁: int ::
                              (  0 <= i₁
                                && 0 <= i₁
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
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < alength
                                     ==> a[pos] == b₅[pos] - 1))
                            && (forall pos: int ::
                                  (  0 <= alength
                                    && 0 <= pos
                                    && pos < alength
                                     ==> b₅[pos] == a[pos] + 1))))))));


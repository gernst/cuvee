goal (forall b: [int]int, length: int, a: [int]int ::
      (  0 <= length
        && true
        && true
        && true
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= length
          && (forall x₂: int ::
                ((exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                   ==> (exists i₁: int ::
                          i₁ < length
                          && b[i₁] != 0
                          && 0 <= i₁
                          && x₂ == i₁
                          && 0 <= i₁
                          && i₁ < 0
                          && a[x₂] == b[i₁])))
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
                   ==> i₁ < length
                    && b[i₁] != 0))
          && (forall a₅: [int]int, i₆: int ::
                (  0 <= i₆
                  && 0 <= i₆
                  && i₆ <= length
                  && (forall x₂: int ::
                        ((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₆)
                           ==> (exists i₁: int ::
                                  i₁ < length
                                  && b[i₁] != 0
                                  && 0 <= i₁
                                  && x₂ == i₁
                                  && 0 <= i₁
                                  && i₁ < i₆
                                  && a₅[x₂] == b[i₁])))
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
                           ==> i₁ < length
                            && b[i₁] != 0))
                   ==> (  i₆ < length
                      && b[i₆] != 0
                       ==> 0 <= i₆ + 1
                        && 0 <= i₆ + 1
                        && i₆ + 1 <= length
                        && (forall x₂: int ::
                              ((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₆ + 1)
                                 ==> (exists i₁: int ::
                                        i₁ < length
                                        && b[i₁] != 0
                                        && 0 <= i₁
                                        && x₂ == i₁
                                        && 0 <= i₁
                                        && i₁ < i₆ + 1
                                        && a₅[i₆ := b[i₆]][x₂] == b[i₁])))
                        && (forall x₂: int ::
                              (!((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₆ + 1)
                              )
                                 ==> a₅[i₆ := b[i₆]][x₂] == a[x₂]))
                        && (forall i₁: int ::
                              (  0 <= i₁
                                && i₁ <= i₁
                                && 0 <= i₁
                                && i₁ < i₆ + 1
                                 ==> i₁ < length
                                  && b[i₁] != 0))
                        && true
                        && (true
                           ==> true))
                    && (!(  i₆ < length
                      && b[i₆] != 0
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall pos: int ::
                                  (  0 <= length
                                    && 0 <= pos
                                    && pos < i₆
                                     ==> a₅[pos] == b[pos]))
                            && (forall pos: int ::
                                  (  0 <= length
                                    && 0 <= pos
                                    && pos < i₆
                                     ==> a₅[pos] != 0))
                            && (forall pos: int ::
                                  (  0 <= length
                                    && 0 <= pos
                                    && pos < i₆
                                     ==> b[pos] != 0))
                            && (  0 <= length
                              && i₆ < length
                               ==> b[i₆] == 0)))))));


goal (forall b: [int]int, blength: int, a: [int]int ::
      (  0 <= blength
        && true
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= blength
          && (forall x₂: int ::
                ((exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                   ==> (exists i₁: int ::
                            b[i₁] < 0
                            && i₁ < blength
                            && 0 <= i₁
                            && x₂ == i₁
                            && 0 <= i₁
                            && i₁ < 0
                            && a[x₂] == b[i₁])
                    || (exists i₁: int ::
                            !(b[i₁] < 0
                            )
                            && i₁ < blength
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
                   ==> i₁ < blength))
          && (forall a₅: [int]int, i₆: int ::
                (  0 <= i₆
                  && 0 <= i₆
                  && i₆ <= blength
                  && (forall x₂: int ::
                        ((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₆)
                           ==> (exists i₁: int ::
                                    b[i₁] < 0
                                    && i₁ < blength
                                    && 0 <= i₁
                                    && x₂ == i₁
                                    && 0 <= i₁
                                    && i₁ < i₆
                                    && a₅[x₂] == b[i₁])
                            || (exists i₁: int ::
                                    !(b[i₁] < 0
                                    )
                                    && i₁ < blength
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
                           ==> i₁ < blength))
                   ==> (i₆ < blength
                       ==> (b[i₆] < 0
                           ==> 0 <= i₆ + 1
                            && 0 <= i₆ + 1
                            && i₆ + 1 <= blength
                            && (forall x₂: int ::
                                  ((exists i₁: int ::
                                          x₂ == i₁
                                          && 0 <= i₁
                                          && i₁ < i₆ + 1)
                                     ==> (exists i₁: int ::
                                              b[i₁] < 0
                                              && i₁ < blength
                                              && 0 <= i₁
                                              && x₂ == i₁
                                              && 0 <= i₁
                                              && i₁ < i₆ + 1
                                              && a₅[i₆ := b[i₆]][x₂] == b[i₁])
                                      || (exists i₁: int ::
                                              !(b[i₁] < 0
                                              )
                                              && i₁ < blength
                                              && 0 <= i₁
                                              && x₂ == i₁
                                              && 0 <= i₁
                                              && i₁ < i₆ + 1
                                              && a₅[i₆ := b[i₆]][x₂] == 0)))
                            && (forall x₂: int ::
                                  (!((exists i₁: int ::
                                          x₂ == i₁
                                          && 0 <= i₁
                                          && i₁ < i₆ + 1)
                                  )
                                     ==> a₅[i₆ := b[i₆]][x₂] == a[x₂]))
                            && (forall i₁: int ::
                                  (  0 <= i₁
                                    && 0 <= i₁
                                    && i₁ < i₆ + 1
                                     ==> i₁ < blength))
                            && true
                            && (true
                               ==> true))
                        && (!(b[i₆] < 0
                        )
                           ==> 0 <= i₆ + 1
                            && 0 <= i₆ + 1
                            && i₆ + 1 <= blength
                            && (forall x₂: int ::
                                  ((exists i₁: int ::
                                          x₂ == i₁
                                          && 0 <= i₁
                                          && i₁ < i₆ + 1)
                                     ==> (exists i₁: int ::
                                              b[i₁] < 0
                                              && i₁ < blength
                                              && 0 <= i₁
                                              && x₂ == i₁
                                              && 0 <= i₁
                                              && i₁ < i₆ + 1
                                              && a₅[i₆ := 0][x₂] == b[i₁])
                                      || (exists i₁: int ::
                                              !(b[i₁] < 0
                                              )
                                              && i₁ < blength
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
                                     ==> i₁ < blength))
                            && true
                            && (true
                               ==> true)))
                    && (!(i₆ < blength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall pos: int ::
                                  (  0 <= pos
                                    && pos < blength
                                    && 0 <= blength
                                     ==> a₅[pos] <= 0))
                            && (forall pos: int ::
                                  (  0 <= pos
                                    && pos < blength
                                    && 0 <= blength
                                     ==> a₅[pos] == 0
                                      || a₅[pos] == b[pos]))))))));


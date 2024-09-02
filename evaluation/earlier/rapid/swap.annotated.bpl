goal (forall length: int, a: [int]int, b: [int]int ::
      (  0 <= length
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
          && (forall x₃: int ::
                ((exists i₁: int ::
                        x₃ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                   ==> (exists i₁: int ::
                          i₁ < length
                          && 0 <= i₁
                          && x₃ == i₁
                          && 0 <= i₁
                          && i₁ < 0
                          && b[x₃] == a[i₁])))
          && (forall x₃: int ::
                (!((exists i₁: int ::
                        x₃ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                )
                   ==> b[x₃] == b[x₃]))
          && (forall i₁: int ::
                (  0 <= i₁
                  && 0 <= i₁
                  && i₁ < 0
                   ==> i₁ < length))
          && (forall a₇: [int]int, b₈: [int]int, i₉: int ::
                (  0 <= i₉
                  && 0 <= i₉
                  && i₉ <= length
                  && (forall x₂: int ::
                        ((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₉)
                           ==> (exists i₁: int ::
                                  i₁ < length
                                  && 0 <= i₁
                                  && x₂ == i₁
                                  && 0 <= i₁
                                  && i₁ < i₉
                                  && a₇[x₂] == b[i₁])))
                  && (forall x₂: int ::
                        (!((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₉)
                        )
                           ==> a₇[x₂] == a[x₂]))
                  && (forall x₃: int ::
                        ((exists i₁: int ::
                                x₃ == i₁
                                && 0 <= i₁
                                && i₁ < i₉)
                           ==> (exists i₁: int ::
                                  i₁ < length
                                  && 0 <= i₁
                                  && x₃ == i₁
                                  && 0 <= i₁
                                  && i₁ < i₉
                                  && b₈[x₃] == a[i₁])))
                  && (forall x₃: int ::
                        (!((exists i₁: int ::
                                x₃ == i₁
                                && 0 <= i₁
                                && i₁ < i₉)
                        )
                           ==> b₈[x₃] == b[x₃]))
                  && (forall i₁: int ::
                        (  0 <= i₁
                          && 0 <= i₁
                          && i₁ < i₉
                           ==> i₁ < length))
                   ==> (i₉ < length
                       ==> 0 <= i₉ + 1
                        && 0 <= i₉ + 1
                        && i₉ + 1 <= length
                        && (forall x₂: int ::
                              ((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₉ + 1)
                                 ==> (exists i₁: int ::
                                        i₁ < length
                                        && 0 <= i₁
                                        && x₂ == i₁
                                        && 0 <= i₁
                                        && i₁ < i₉ + 1
                                        && a₇[i₉ := b₈[i₉]][x₂] == b[i₁])))
                        && (forall x₂: int ::
                              (!((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₉ + 1)
                              )
                                 ==> a₇[i₉ := b₈[i₉]][x₂] == a[x₂]))
                        && (forall x₃: int ::
                              ((exists i₁: int ::
                                      x₃ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₉ + 1)
                                 ==> (exists i₁: int ::
                                        i₁ < length
                                        && 0 <= i₁
                                        && x₃ == i₁
                                        && 0 <= i₁
                                        && i₁ < i₉ + 1
                                        && b₈[i₉ := a₇[i₉]][x₃] == a[i₁])))
                        && (forall x₃: int ::
                              (!((exists i₁: int ::
                                      x₃ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₉ + 1)
                              )
                                 ==> b₈[i₉ := a₇[i₉]][x₃] == b[x₃]))
                        && (forall i₁: int ::
                              (  0 <= i₁
                                && 0 <= i₁
                                && i₁ < i₉ + 1
                                 ==> i₁ < length))
                        && true
                        && (true
                           ==> true))
                    && (!(i₉ < length
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall pos: int ::
                                  (  0 <= length
                                    && 0 <= pos
                                    && pos < length
                                     ==> a₇[pos] == b[pos]))
                            && (forall pos: int ::
                                  (  0 <= length
                                    && 0 <= pos
                                    && pos < length
                                     ==> b₈[pos] == a[pos]))))))));


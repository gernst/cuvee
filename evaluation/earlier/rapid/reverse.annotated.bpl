goal (forall b: [int]int, length: int, a: [int]int ::
      (  0 <= length
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
                          && a[x₂] == b[-1 + length + -i₁])))
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
                   ==> i₁ < length))
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
                                  && 0 <= i₁
                                  && x₂ == i₁
                                  && 0 <= i₁
                                  && i₁ < i₆
                                  && a₅[x₂] == b[-1 + length + -i₁])))
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
                           ==> i₁ < length))
                   ==> (i₆ < length
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
                                        && 0 <= i₁
                                        && x₂ == i₁
                                        && 0 <= i₁
                                        && i₁ < i₆ + 1
                                        && a₅[i₆ := b[length - 1 - i₆]][x₂] == b[-1 + length + -i₁])))
                        && (forall x₂: int ::
                              (!((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₆ + 1)
                              )
                                 ==> a₅[i₆ := b[length - 1 - i₆]][x₂] == a[x₂]))
                        && (forall i₁: int ::
                              (  0 <= i₁
                                && i₁ <= i₁
                                && 0 <= i₁
                                && i₁ < i₆ + 1
                                 ==> i₁ < length))
                        && true
                        && (true
                           ==> true))
                    && (!(i₆ < length
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall j: int ::
                                  (  0 <= length
                                    && 0 <= j
                                    && j < length
                                     ==> a₅[j] == b[length - 1 - j]))))))));


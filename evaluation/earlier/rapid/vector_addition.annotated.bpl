goal (forall a: [int]int, b: [int]int, length: int, c: [int]int ::
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
                          && c[x₂] == a[i₁] + b[i₁])))
          && (forall x₂: int ::
                (!((exists i₁: int ::
                        x₂ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                )
                   ==> c[x₂] == c[x₂]))
          && (forall i₁: int ::
                (  0 <= i₁
                  && i₁ <= i₁
                  && 0 <= i₁
                  && i₁ < 0
                   ==> i₁ < length))
          && (forall c₅: [int]int, i₆: int ::
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
                                  && c₅[x₂] == a[i₁] + b[i₁])))
                  && (forall x₂: int ::
                        (!((exists i₁: int ::
                                x₂ == i₁
                                && 0 <= i₁
                                && i₁ < i₆)
                        )
                           ==> c₅[x₂] == c[x₂]))
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
                                        && c₅[i₆ := a[i₆] + b[i₆]][x₂] == a[i₁] + b[i₁])))
                        && (forall x₂: int ::
                              (!((exists i₁: int ::
                                      x₂ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₆ + 1)
                              )
                                 ==> c₅[i₆ := a[i₆] + b[i₆]][x₂] == c[x₂]))
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
                                  (  0 <= j
                                    && j < length
                                    && 0 <= length
                                     ==> c₅[j] == a[j] + b[j]))))))));


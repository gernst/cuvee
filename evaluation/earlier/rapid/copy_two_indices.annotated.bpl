goal (forall b: [int]int, blength: int, a: [int]int ::
      (  0 <= blength
        && true
         ==> 0 <= 0
          && 0 == 0
          && 0 <= 0
          && 0 <= 0
          && 0 <= blength
          && (forall x₃: int ::
                ((exists i₁: int ::
                        x₃ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                   ==> (exists i₁: int, j₂: int ::
                          i₁ < blength
                          && 0 <= i₁
                          && i₁ == j₂
                          && x₃ == i₁
                          && 0 <= i₁
                          && i₁ < 0
                          && a[x₃] == b[j₂])))
          && (forall x₃: int ::
                (!((exists i₁: int ::
                        x₃ == i₁
                        && 0 <= i₁
                        && i₁ < 0)
                )
                   ==> a[x₃] == a[x₃]))
          && (forall i₁: int, j₂: int ::
                (  0 <= i₁
                  && i₁ == j₂
                  && 0 <= i₁
                  && i₁ < 0
                  && 0 <= j₂
                  && j₂ < 0
                   ==> i₁ < blength))
          && (forall a₇: [int]int, i₈: int, j₉: int ::
                (  0 <= i₈
                  && i₈ == j₉
                  && 0 <= i₈
                  && 0 <= j₉
                  && i₈ <= blength
                  && (forall x₃: int ::
                        ((exists i₁: int ::
                                x₃ == i₁
                                && 0 <= i₁
                                && i₁ < i₈)
                           ==> (exists i₁: int, j₂: int ::
                                  i₁ < blength
                                  && 0 <= i₁
                                  && i₁ == j₂
                                  && x₃ == i₁
                                  && 0 <= i₁
                                  && i₁ < i₈
                                  && a₇[x₃] == b[j₂])))
                  && (forall x₃: int ::
                        (!((exists i₁: int ::
                                x₃ == i₁
                                && 0 <= i₁
                                && i₁ < i₈)
                        )
                           ==> a₇[x₃] == a[x₃]))
                  && (forall i₁: int, j₂: int ::
                        (  0 <= i₁
                          && i₁ == j₂
                          && 0 <= i₁
                          && i₁ < i₈
                          && 0 <= j₂
                          && j₂ < j₉
                           ==> i₁ < blength))
                   ==> (i₈ < blength
                       ==> 0 <= i₈ + 1
                        && i₈ + 1 == j₉ + 1
                        && 0 <= i₈ + 1
                        && 0 <= j₉ + 1
                        && i₈ + 1 <= blength
                        && (forall x₃: int ::
                              ((exists i₁: int ::
                                      x₃ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₈ + 1)
                                 ==> (exists i₁: int, j₂: int ::
                                        i₁ < blength
                                        && 0 <= i₁
                                        && i₁ == j₂
                                        && x₃ == i₁
                                        && 0 <= i₁
                                        && i₁ < i₈ + 1
                                        && a₇[i₈ := b[j₉]][x₃] == b[j₂])))
                        && (forall x₃: int ::
                              (!((exists i₁: int ::
                                      x₃ == i₁
                                      && 0 <= i₁
                                      && i₁ < i₈ + 1)
                              )
                                 ==> a₇[i₈ := b[j₉]][x₃] == a[x₃]))
                        && (forall i₁: int, j₂: int ::
                              (  0 <= i₁
                                && i₁ == j₂
                                && 0 <= i₁
                                && i₁ < i₈ + 1
                                && 0 <= j₂
                                && j₂ < j₉ + 1
                                 ==> i₁ < blength))
                        && true
                        && (true
                           ==> true))
                    && (!(i₈ < blength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall k: int ::
                                  (  0 <= blength
                                    && 0 <= k
                                    && k < blength
                                     ==> a₇[k] == b[k]))))))));


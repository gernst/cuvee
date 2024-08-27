goal (forall blength: int, b: [int]int, a: [int]int ::
      (0 <= blength
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= blength
          && (forall x₂: int, i₁: int ::
                (  x₂ == i₁
                  && 0 <= i₁
                  && i₁ < 0
                   ==> (exists i₁: int ::
                            b[i₁] >= 0
                            && i₁ < blength
                            && 0 <= i₁
                            && x₂ == i₁
                            && i₁ < 0
                            && a[x₂] == b[i₁])
                    || (exists i₁: int ::
                          (b[i₁] >= 0
                             ==> false))))
          && (forall x₂: int ::
                  (exists i₁: int ::
                          x₂ == i₁
                          && 0 <= i₁
                          && i₁ < 0)
                  || a[x₂] == a[x₂])
          && (forall i₁: int ::
                (  0 <= i₁
                  && i₁ < 0
                   ==> i₁ < blength))
          && (forall a₅: [int]int, i₆: int ::
                (  0 <= i₆
                  && 0 <= i₆
                  && i₆ <= blength
                  && (forall x₂: int, i₁: int ::
                        (  x₂ == i₁
                          && 0 <= i₁
                          && i₁ < i₆
                           ==> (exists i₁: int ::
                                    b[i₁] >= 0
                                    && i₁ < blength
                                    && 0 <= i₁
                                    && x₂ == i₁
                                    && i₁ < i₆
                                    && a₅[x₂] == b[i₁])
                            || (exists i₁: int ::
                                  (b[i₁] >= 0
                                     ==> false))))
                  && (forall x₂: int ::
                          (exists i₁: int ::
                                  x₂ == i₁
                                  && 0 <= i₁
                                  && i₁ < i₆)
                          || a₅[x₂] == a[x₂])
                  && (forall i₁: int ::
                        (  0 <= i₁
                          && i₁ < i₆
                           ==> i₁ < blength))
                   ==> (i₆ < blength
                       ==> (b[i₆] >= 0
                           ==> 0 <= i₆ + 1
                            && 0 <= i₆ + 1
                            && i₆ + 1 <= blength
                            && (forall x₂: int, i₁: int ::
                                  (  x₂ == i₁
                                    && 0 <= i₁
                                    && i₁ < i₆ + 1
                                     ==> (exists i₁: int ::
                                              b[i₁] >= 0
                                              && i₁ < blength
                                              && 0 <= i₁
                                              && x₂ == i₁
                                              && i₁ < i₆ + 1
                                              && a₅[i₆ := b[i₆]][x₂] == b[i₁])
                                      || (exists i₁: int ::
                                            (b[i₁] >= 0
                                               ==> false))))
                            && (forall x₂: int ::
                                    (exists i₁: int ::
                                            x₂ == i₁
                                            && 0 <= i₁
                                            && i₁ < i₆ + 1)
                                    || a₅[i₆ := b[i₆]][x₂] == a[x₂])
                            && (forall i₁: int ::
                                  (  0 <= i₁
                                    && i₁ < i₆ + 1
                                     ==> i₁ < blength)))
                        &&   b[i₆] >= 0
                          ||   0 <= i₆ + 1
                            && 0 <= i₆ + 1
                            && i₆ + 1 <= blength
                            && (forall x₂: int, i₁: int ::
                                  (  x₂ == i₁
                                    && 0 <= i₁
                                    && i₁ < i₆ + 1
                                     ==> (exists i₁: int ::
                                              b[i₁] >= 0
                                              && i₁ < blength
                                              && 0 <= i₁
                                              && x₂ == i₁
                                              && i₁ < i₆ + 1
                                              && a₅[i₆ := 0 - b[i₆]][x₂] == b[i₁])
                                      || (exists i₁: int ::
                                            (b[i₁] >= 0
                                               ==> false))))
                            && (forall x₂: int ::
                                    (exists i₁: int ::
                                            x₂ == i₁
                                            && 0 <= i₁
                                            && i₁ < i₆ + 1)
                                    || a₅[i₆ := 0 - b[i₆]][x₂] == a[x₂])
                            && (forall i₁: int ::
                                  (  0 <= i₁
                                    && i₁ < i₆ + 1
                                     ==> i₁ < blength)))
                    &&   i₆ < blength
                      ||   (forall k: int ::
                              (  0 <= k
                                && k < blength
                                 ==> a₅[k] == b[k]
                                  || a₅[k] == 0 - b[k]))
                        && (forall k: int ::
                              (  0 <= k
                                && k < blength
                                 ==> 0 <= a₅[k]))))));


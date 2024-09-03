goal (forall a: [int]int, alength: int, b: [int]int ::
      (  0 <= alength
        && true
        && true
        && true
         ==> 0 <= 0
          && 0 <= 0
          && 0 <= alength
          && (forall x₃: int ::
                ((exists i₂: int ::
                        x₃ == i₂
                        && 0 <= i₂
                        && i₂ < 0)
                   ==> (exists m₁: int, i₂: int ::
                            a[i₂] > a[m₁]
                            && i₂ < alength
                            && 0 <= i₂
                            && x₃ == i₂
                            && 0 <= i₂
                            && i₂ < 0
                            && b[x₃] == a[i₂])
                    || (exists m₁: int, i₂: int ::
                            !(a[i₂] > a[m₁]
                            )
                            && i₂ < alength
                            && 0 <= i₂
                            && x₃ == i₂
                            && 0 <= i₂
                            && i₂ < 0
                            && b[x₃] == a[m₁])))
          && (forall x₃: int ::
                (!((exists i₂: int ::
                        x₃ == i₂
                        && 0 <= i₂
                        && i₂ < 0)
                )
                   ==> b[x₃] == b[x₃]))
          && (forall i₂: int ::
                (  0 <= i₂
                  && i₂ <= i₂
                  && 0 <= i₂
                  && i₂ < 0
                   ==> i₂ < alength))
          && (forall b₇: [int]int, m₈: int, i₉: int ::
                (  0 <= i₉
                  && 0 <= i₉
                  && i₉ <= alength
                  && (forall x₃: int ::
                        ((exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₉)
                           ==> (exists m₁: int, i₂: int ::
                                    a[i₂] > a[m₁]
                                    && i₂ < alength
                                    && 0 <= i₂
                                    && x₃ == i₂
                                    && 0 <= i₂
                                    && i₂ < i₉
                                    && b₇[x₃] == a[i₂])
                            || (exists m₁: int, i₂: int ::
                                    !(a[i₂] > a[m₁]
                                    )
                                    && i₂ < alength
                                    && 0 <= i₂
                                    && x₃ == i₂
                                    && 0 <= i₂
                                    && i₂ < i₉
                                    && b₇[x₃] == a[m₁])))
                  && (forall x₃: int ::
                        (!((exists i₂: int ::
                                x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₉)
                        )
                           ==> b₇[x₃] == b[x₃]))
                  && (forall i₂: int ::
                        (  0 <= i₂
                          && i₂ <= i₂
                          && 0 <= i₂
                          && i₂ < i₉
                           ==> i₂ < alength))
                   ==> (i₉ < alength
                       ==> (a[i₉] > a[m₈]
                           ==> 0 <= i₉ + 1
                            && 0 <= i₉ + 1
                            && i₉ + 1 <= alength
                            && (forall x₃: int ::
                                  ((exists i₂: int ::
                                          x₃ == i₂
                                          && 0 <= i₂
                                          && i₂ < i₉ + 1)
                                     ==> (exists m₁: int, i₂: int ::
                                              a[i₂] > a[m₁]
                                              && i₂ < alength
                                              && 0 <= i₂
                                              && x₃ == i₂
                                              && 0 <= i₂
                                              && i₂ < i₉ + 1
                                              && b₇[i₉ := a[i₉]][x₃] == a[i₂])
                                      || (exists m₁: int, i₂: int ::
                                              !(a[i₂] > a[m₁]
                                              )
                                              && i₂ < alength
                                              && 0 <= i₂
                                              && x₃ == i₂
                                              && 0 <= i₂
                                              && i₂ < i₉ + 1
                                              && b₇[i₉ := a[i₉]][x₃] == a[m₁])))
                            && (forall x₃: int ::
                                  (!((exists i₂: int ::
                                          x₃ == i₂
                                          && 0 <= i₂
                                          && i₂ < i₉ + 1)
                                  )
                                     ==> b₇[i₉ := a[i₉]][x₃] == b[x₃]))
                            && (forall i₂: int ::
                                  (  0 <= i₂
                                    && i₂ <= i₂
                                    && 0 <= i₂
                                    && i₂ < i₉ + 1
                                     ==> i₂ < alength))
                            && true
                            && (true
                               ==> true))
                        && (!(a[i₉] > a[m₈]
                        )
                           ==> 0 <= i₉ + 1
                            && 0 <= i₉ + 1
                            && i₉ + 1 <= alength
                            && (forall x₃: int ::
                                  ((exists i₂: int ::
                                          x₃ == i₂
                                          && 0 <= i₂
                                          && i₂ < i₉ + 1)
                                     ==> (exists m₁: int, i₂: int ::
                                              a[i₂] > a[m₁]
                                              && i₂ < alength
                                              && 0 <= i₂
                                              && x₃ == i₂
                                              && 0 <= i₂
                                              && i₂ < i₉ + 1
                                              && b₇[i₉ := a[m₈]][x₃] == a[i₂])
                                      || (exists m₁: int, i₂: int ::
                                              !(a[i₂] > a[m₁]
                                              )
                                              && i₂ < alength
                                              && 0 <= i₂
                                              && x₃ == i₂
                                              && 0 <= i₂
                                              && i₂ < i₉ + 1
                                              && b₇[i₉ := a[m₈]][x₃] == a[m₁])))
                            && (forall x₃: int ::
                                  (!((exists i₂: int ::
                                          x₃ == i₂
                                          && 0 <= i₂
                                          && i₂ < i₉ + 1)
                                  )
                                     ==> b₇[i₉ := a[m₈]][x₃] == b[x₃]))
                            && (forall i₂: int ::
                                  (  0 <= i₂
                                    && i₂ <= i₂
                                    && 0 <= i₂
                                    && i₂ < i₉ + 1
                                     ==> i₂ < alength))
                            && true
                            && (true
                               ==> true)))
                    && (!(i₉ < alength
                    )
                       ==> true
                        && (true
                           ==> true
                            && (forall j: int, k: int ::
                                  (  0 <= alength
                                    && 0 <= j
                                    && 0 <= k
                                    && j <= k
                                    && k < alength
                                     ==> a[j] <= b₇[k]))
                            && (forall j: int ::
                                  (exists k: int ::
                                        (  0 <= alength
                                          && 0 <= j
                                          && j < alength
                                           ==> 0 <= k
                                            && k <= j
                                            && b₇[j] == a[k])))
                            && (forall j: int, k: int ::
                                  (  0 <= alength
                                    && 0 <= j
                                    && 0 <= k
                                    && j <= k
                                    && k < alength
                                     ==> b₇[j] <= b₇[k]))))))));


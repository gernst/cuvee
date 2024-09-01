data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
      (forall b: [int]int ::
              true
              && 0 <= 0
              && 0 <= 100000
              && (forall x₅: int ::
                    ((exists i₄: int ::
                            x₅ == i₄
                            && 0 <= i₄
                            && i₄ < 0)
                       ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                              i₄ < 100000
                              && x₅ == i₄
                              && 0 <= i₄
                              && i₄ < 0
                              && a[x₅] == __VERIFIER_nondet_int₁₃)))
              && (forall x₅: int ::
                    (!((exists i₄: int ::
                            x₅ == i₄
                            && 0 <= i₄
                            && i₄ < 0)
                    )
                       ==> a[x₅] == a[x₅]))
              && (forall i₄: int ::
                    (  i₄ <= i₄
                      && 0 <= i₄
                      && i₄ < 0
                       ==> i₄ < 100000))
              && (forall a₁₆: [int]int, i₁₇: int ::
                    (  true
                      && 0 <= i₁₇
                      && i₁₇ <= 100000
                      && (forall x₅: int ::
                            ((exists i₄: int ::
                                    x₅ == i₄
                                    && 0 <= i₄
                                    && i₄ < i₁₇)
                               ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                      i₄ < 100000
                                      && x₅ == i₄
                                      && 0 <= i₄
                                      && i₄ < i₁₇
                                      && a₁₆[x₅] == __VERIFIER_nondet_int₁₃)))
                      && (forall x₅: int ::
                            (!((exists i₄: int ::
                                    x₅ == i₄
                                    && 0 <= i₄
                                    && i₄ < i₁₇)
                            )
                               ==> a₁₆[x₅] == a[x₅]))
                      && (forall i₄: int ::
                            (  i₄ <= i₄
                              && 0 <= i₄
                              && i₄ < i₁₇
                               ==> i₄ < 100000))
                       ==> (i₁₇ < 100000
                           ==> (forall __VERIFIER_nondet_int₁: int ::
                                  true
                                  && 0 <= i₁₇ + 1
                                  && i₁₇ + 1 <= 100000
                                  && (forall x₅: int ::
                                        ((exists i₄: int ::
                                                x₅ == i₄
                                                && 0 <= i₄
                                                && i₄ < i₁₇ + 1)
                                           ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                                  i₄ < 100000
                                                  && x₅ == i₄
                                                  && 0 <= i₄
                                                  && i₄ < i₁₇ + 1
                                                  && a₁₆[i₁₇ := __VERIFIER_nondet_int₁][x₅] == __VERIFIER_nondet_int₁₃)))
                                  && (forall x₅: int ::
                                        (!((exists i₄: int ::
                                                x₅ == i₄
                                                && 0 <= i₄
                                                && i₄ < i₁₇ + 1)
                                        )
                                           ==> a₁₆[i₁₇ := __VERIFIER_nondet_int₁][x₅] == a[x₅]))
                                  && (forall i₄: int ::
                                        (  i₄ <= i₄
                                          && 0 <= i₄
                                          && i₄ < i₁₇ + 1
                                           ==> i₄ < 100000))
                                  && true
                                  && (true
                                     ==> true)))
                        && (!(i₁₇ < 100000
                        )
                           ==> true
                            && (true
                               ==> true
                                && 0 <= 0
                                && 0 <= 100000
                                && (forall x₉: int ::
                                      ((exists i₈: int ::
                                              x₉ == i₈
                                              && 0 <= i₈
                                              && i₈ < 0)
                                         ==> (exists i₈: int ::
                                                  0 <= a₁₆[i₈]
                                                  && i₈ < 100000
                                                  && x₉ == i₈
                                                  && 0 <= i₈
                                                  && i₈ < 0
                                                  && b[x₉] == 1)
                                          || (exists i₈: int ::
                                                  !(0 <= a₁₆[i₈]
                                                  )
                                                  && i₈ < 100000
                                                  && x₉ == i₈
                                                  && 0 <= i₈
                                                  && i₈ < 0
                                                  && b[x₉] == 0)))
                                && (forall x₉: int ::
                                      (!((exists i₈: int ::
                                              x₉ == i₈
                                              && 0 <= i₈
                                              && i₈ < 0)
                                      )
                                         ==> b[x₉] == b[x₉]))
                                && (forall i₈: int ::
                                      (  i₈ <= i₈
                                        && 0 <= i₈
                                        && i₈ < 0
                                         ==> i₈ < 100000))
                                && (forall b₁₈: [int]int, i₁₉: int ::
                                      (  true
                                        && 0 <= i₁₉
                                        && i₁₉ <= 100000
                                        && (forall x₉: int ::
                                              ((exists i₈: int ::
                                                      x₉ == i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₉)
                                                 ==> (exists i₈: int ::
                                                          0 <= a₁₆[i₈]
                                                          && i₈ < 100000
                                                          && x₉ == i₈
                                                          && 0 <= i₈
                                                          && i₈ < i₁₉
                                                          && b₁₈[x₉] == 1)
                                                  || (exists i₈: int ::
                                                          !(0 <= a₁₆[i₈]
                                                          )
                                                          && i₈ < 100000
                                                          && x₉ == i₈
                                                          && 0 <= i₈
                                                          && i₈ < i₁₉
                                                          && b₁₈[x₉] == 0)))
                                        && (forall x₉: int ::
                                              (!((exists i₈: int ::
                                                      x₉ == i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₉)
                                              )
                                                 ==> b₁₈[x₉] == b[x₉]))
                                        && (forall i₈: int ::
                                              (  i₈ <= i₈
                                                && 0 <= i₈
                                                && i₈ < i₁₉
                                                 ==> i₈ < 100000))
                                         ==> (i₁₉ < 100000
                                             ==> (0 <= a₁₆[i₁₉]
                                                 ==> true
                                                  && 0 <= i₁₉ + 1
                                                  && i₁₉ + 1 <= 100000
                                                  && (forall x₉: int ::
                                                        ((exists i₈: int ::
                                                                x₉ == i₈
                                                                && 0 <= i₈
                                                                && i₈ < i₁₉ + 1)
                                                           ==> (exists i₈: int ::
                                                                    0 <= a₁₆[i₈]
                                                                    && i₈ < 100000
                                                                    && x₉ == i₈
                                                                    && 0 <= i₈
                                                                    && i₈ < i₁₉ + 1
                                                                    && b₁₈[i₁₉ := 1][x₉] == 1)
                                                            || (exists i₈: int ::
                                                                    !(0 <= a₁₆[i₈]
                                                                    )
                                                                    && i₈ < 100000
                                                                    && x₉ == i₈
                                                                    && 0 <= i₈
                                                                    && i₈ < i₁₉ + 1
                                                                    && b₁₈[i₁₉ := 1][x₉] == 0)))
                                                  && (forall x₉: int ::
                                                        (!((exists i₈: int ::
                                                                x₉ == i₈
                                                                && 0 <= i₈
                                                                && i₈ < i₁₉ + 1)
                                                        )
                                                           ==> b₁₈[i₁₉ := 1][x₉] == b[x₉]))
                                                  && (forall i₈: int ::
                                                        (  i₈ <= i₈
                                                          && 0 <= i₈
                                                          && i₈ < i₁₉ + 1
                                                           ==> i₈ < 100000))
                                                  && true
                                                  && (true
                                                     ==> true))
                                              && (!(0 <= a₁₆[i₁₉]
                                              )
                                                 ==> true
                                                  && 0 <= i₁₉ + 1
                                                  && i₁₉ + 1 <= 100000
                                                  && (forall x₉: int ::
                                                        ((exists i₈: int ::
                                                                x₉ == i₈
                                                                && 0 <= i₈
                                                                && i₈ < i₁₉ + 1)
                                                           ==> (exists i₈: int ::
                                                                    0 <= a₁₆[i₈]
                                                                    && i₈ < 100000
                                                                    && x₉ == i₈
                                                                    && 0 <= i₈
                                                                    && i₈ < i₁₉ + 1
                                                                    && b₁₈[i₁₉ := 0][x₉] == 1)
                                                            || (exists i₈: int ::
                                                                    !(0 <= a₁₆[i₈]
                                                                    )
                                                                    && i₈ < 100000
                                                                    && x₉ == i₈
                                                                    && 0 <= i₈
                                                                    && i₈ < i₁₉ + 1
                                                                    && b₁₈[i₁₉ := 0][x₉] == 0)))
                                                  && (forall x₉: int ::
                                                        (!((exists i₈: int ::
                                                                x₉ == i₈
                                                                && 0 <= i₈
                                                                && i₈ < i₁₉ + 1)
                                                        )
                                                           ==> b₁₈[i₁₉ := 0][x₉] == b[x₉]))
                                                  && (forall i₈: int ::
                                                        (  i₈ <= i₈
                                                          && 0 <= i₈
                                                          && i₈ < i₁₉ + 1
                                                           ==> i₈ < 100000))
                                                  && true
                                                  && (true
                                                     ==> true)))
                                          && (!(i₁₉ < 100000
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= 100000
                                                  && (forall i₁₃: int ::
                                                        (  i₁₃ <= i₁₃
                                                          && 0 <= i₁₃
                                                          && i₁₃ < 0
                                                           ==> i₁₃ < 100000))
                                                  && (forall f₂₀: int, i₂₁: int ::
                                                        (  true
                                                          && 0 <= i₂₁
                                                          && i₂₁ <= 100000
                                                          && (forall i₁₃: int ::
                                                                (  i₁₃ <= i₁₃
                                                                  && 0 <= i₁₃
                                                                  && i₁₃ < i₂₁
                                                                   ==> i₁₃ < 100000))
                                                           ==> (i₂₁ < 100000
                                                               ==> (  0 <= a₁₆[i₂₁]
                                                                  && !(b₁₈[i₂₁] != 0
                                                                  )
                                                                   ==> (  a₁₆[i₂₁] < 0
                                                                      && b₁₈[i₂₁] != 0
                                                                       ==> true
                                                                        && 0 <= i₂₁ + 1
                                                                        && i₂₁ + 1 <= 100000
                                                                        && (forall i₁₃: int ::
                                                                              (  i₁₃ <= i₁₃
                                                                                && 0 <= i₁₃
                                                                                && i₁₃ < i₂₁ + 1
                                                                                 ==> i₁₃ < 100000))
                                                                        && true
                                                                        && (true
                                                                           ==> true))
                                                                    && (!(  a₁₆[i₂₁] < 0
                                                                      && b₁₈[i₂₁] != 0
                                                                    )
                                                                       ==> true
                                                                        && 0 <= i₂₁ + 1
                                                                        && i₂₁ + 1 <= 100000
                                                                        && (forall i₁₃: int ::
                                                                              (  i₁₃ <= i₁₃
                                                                                && 0 <= i₁₃
                                                                                && i₁₃ < i₂₁ + 1
                                                                                 ==> i₁₃ < 100000))
                                                                        && true
                                                                        && (true
                                                                           ==> true)))
                                                                && (!(  0 <= a₁₆[i₂₁]
                                                                  && !(b₁₈[i₂₁] != 0
                                                                  )
                                                                )
                                                                   ==> (  a₁₆[i₂₁] < 0
                                                                      && b₁₈[i₂₁] != 0
                                                                       ==> true
                                                                        && 0 <= i₂₁ + 1
                                                                        && i₂₁ + 1 <= 100000
                                                                        && (forall i₁₃: int ::
                                                                              (  i₁₃ <= i₁₃
                                                                                && 0 <= i₁₃
                                                                                && i₁₃ < i₂₁ + 1
                                                                                 ==> i₁₃ < 100000))
                                                                        && true
                                                                        && (true
                                                                           ==> true))
                                                                    && (!(  a₁₆[i₂₁] < 0
                                                                      && b₁₈[i₂₁] != 0
                                                                    )
                                                                       ==> true
                                                                        && 0 <= i₂₁ + 1
                                                                        && i₂₁ + 1 <= 100000
                                                                        && (forall i₁₃: int ::
                                                                              (  i₁₃ <= i₁₃
                                                                                && 0 <= i₁₃
                                                                                && i₁₃ < i₂₁ + 1
                                                                                 ==> i₁₃ < 100000))
                                                                        && true
                                                                        && (true
                                                                           ==> true))))
                                                            && (!(i₂₁ < 100000
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> f₂₀ != 0
                                                                    && (true
                                                                       ==> true)))))))))))))));


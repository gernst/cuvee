data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int ::
      (forall a2: [int]int ::
            (forall a3: [int]int ::
                  (forall a4: [int]int ::
                          true
                          && 0 <= 0
                          && 0 <= 100000
                          && (forall x₈: int ::
                                ((exists a₇: int ::
                                        x₈ == a₇
                                        && 0 <= a₇
                                        && a₇ < 0)
                                   ==> (exists __VERIFIER_nondet_int₁₆: int, a₇: int ::
                                          a₇ < 100000
                                          && x₈ == a₇
                                          && 0 <= a₇
                                          && a₇ < 0
                                          && a1[x₈] == __VERIFIER_nondet_int₁₆)))
                          && (forall x₈: int ::
                                (!((exists a₇: int ::
                                        x₈ == a₇
                                        && 0 <= a₇
                                        && a₇ < 0)
                                )
                                   ==> a1[x₈] == a1[x₈]))
                          && (forall a₇: int ::
                                (  a₇ <= a₇
                                  && 0 <= a₇
                                  && a₇ < 0
                                   ==> a₇ < 100000))
                          && (forall a1₂₇: [int]int, a₂₈: int ::
                                (  true
                                  && 0 <= a₂₈
                                  && a₂₈ <= 100000
                                  && (forall x₈: int ::
                                        ((exists a₇: int ::
                                                x₈ == a₇
                                                && 0 <= a₇
                                                && a₇ < a₂₈)
                                           ==> (exists __VERIFIER_nondet_int₁₆: int, a₇: int ::
                                                  a₇ < 100000
                                                  && x₈ == a₇
                                                  && 0 <= a₇
                                                  && a₇ < a₂₈
                                                  && a1₂₇[x₈] == __VERIFIER_nondet_int₁₆)))
                                  && (forall x₈: int ::
                                        (!((exists a₇: int ::
                                                x₈ == a₇
                                                && 0 <= a₇
                                                && a₇ < a₂₈)
                                        )
                                           ==> a1₂₇[x₈] == a1[x₈]))
                                  && (forall a₇: int ::
                                        (  a₇ <= a₇
                                          && 0 <= a₇
                                          && a₇ < a₂₈
                                           ==> a₇ < 100000))
                                   ==> (a₂₈ < 100000
                                       ==> (forall __VERIFIER_nondet_int₁: int ::
                                              true
                                              && 0 <= a₂₈ + 1
                                              && a₂₈ + 1 <= 100000
                                              && (forall x₈: int ::
                                                    ((exists a₇: int ::
                                                            x₈ == a₇
                                                            && 0 <= a₇
                                                            && a₇ < a₂₈ + 1)
                                                       ==> (exists __VERIFIER_nondet_int₁₆: int, a₇: int ::
                                                              a₇ < 100000
                                                              && x₈ == a₇
                                                              && 0 <= a₇
                                                              && a₇ < a₂₈ + 1
                                                              && a1₂₇[a₂₈ := __VERIFIER_nondet_int₁][x₈] == __VERIFIER_nondet_int₁₆)))
                                              && (forall x₈: int ::
                                                    (!((exists a₇: int ::
                                                            x₈ == a₇
                                                            && 0 <= a₇
                                                            && a₇ < a₂₈ + 1)
                                                    )
                                                       ==> a1₂₇[a₂₈ := __VERIFIER_nondet_int₁][x₈] == a1[x₈]))
                                              && (forall a₇: int ::
                                                    (  a₇ <= a₇
                                                      && 0 <= a₇
                                                      && a₇ < a₂₈ + 1
                                                       ==> a₇ < 100000))
                                              && true
                                              && (true
                                                 ==> true)))
                                    && (!(a₂₈ < 100000
                                    )
                                       ==> true
                                        && (true
                                           ==> true
                                            && 0 <= 0
                                            && 0 <= 100000
                                            && (forall x₁₃: int ::
                                                  ((exists i₁₂: int ::
                                                          x₁₃ == i₁₂
                                                          && 0 <= i₁₂
                                                          && i₁₂ < 0)
                                                     ==> (exists i₁₂: int ::
                                                            i₁₂ < 100000
                                                            && x₁₃ == i₁₂
                                                            && 0 <= i₁₂
                                                            && i₁₂ < 0
                                                            && a2[x₁₃] == a1₂₇[i₁₂])))
                                            && (forall x₁₃: int ::
                                                  (!((exists i₁₂: int ::
                                                          x₁₃ == i₁₂
                                                          && 0 <= i₁₂
                                                          && i₁₂ < 0)
                                                  )
                                                     ==> a2[x₁₃] == a2[x₁₃]))
                                            && (forall i₁₂: int ::
                                                  (  i₁₂ <= i₁₂
                                                    && 0 <= i₁₂
                                                    && i₁₂ < 0
                                                     ==> i₁₂ < 100000))
                                            && (forall a2₂₉: [int]int, i₃₀: int ::
                                                  (  true
                                                    && 0 <= i₃₀
                                                    && i₃₀ <= 100000
                                                    && (forall x₁₃: int ::
                                                          ((exists i₁₂: int ::
                                                                  x₁₃ == i₁₂
                                                                  && 0 <= i₁₂
                                                                  && i₁₂ < i₃₀)
                                                             ==> (exists i₁₂: int ::
                                                                    i₁₂ < 100000
                                                                    && x₁₃ == i₁₂
                                                                    && 0 <= i₁₂
                                                                    && i₁₂ < i₃₀
                                                                    && a2₂₉[x₁₃] == a1₂₇[i₁₂])))
                                                    && (forall x₁₃: int ::
                                                          (!((exists i₁₂: int ::
                                                                  x₁₃ == i₁₂
                                                                  && 0 <= i₁₂
                                                                  && i₁₂ < i₃₀)
                                                          )
                                                             ==> a2₂₉[x₁₃] == a2[x₁₃]))
                                                    && (forall i₁₂: int ::
                                                          (  i₁₂ <= i₁₂
                                                            && 0 <= i₁₂
                                                            && i₁₂ < i₃₀
                                                             ==> i₁₂ < 100000))
                                                     ==> (i₃₀ < 100000
                                                         ==> true
                                                          && 0 <= i₃₀ + 1
                                                          && i₃₀ + 1 <= 100000
                                                          && (forall x₁₃: int ::
                                                                ((exists i₁₂: int ::
                                                                        x₁₃ == i₁₂
                                                                        && 0 <= i₁₂
                                                                        && i₁₂ < i₃₀ + 1)
                                                                   ==> (exists i₁₂: int ::
                                                                          i₁₂ < 100000
                                                                          && x₁₃ == i₁₂
                                                                          && 0 <= i₁₂
                                                                          && i₁₂ < i₃₀ + 1
                                                                          && a2₂₉[i₃₀ := a1₂₇[i₃₀]][x₁₃] == a1₂₇[i₁₂])))
                                                          && (forall x₁₃: int ::
                                                                (!((exists i₁₂: int ::
                                                                        x₁₃ == i₁₂
                                                                        && 0 <= i₁₂
                                                                        && i₁₂ < i₃₀ + 1)
                                                                )
                                                                   ==> a2₂₉[i₃₀ := a1₂₇[i₃₀]][x₁₃] == a2[x₁₃]))
                                                          && (forall i₁₂: int ::
                                                                (  i₁₂ <= i₁₂
                                                                  && 0 <= i₁₂
                                                                  && i₁₂ < i₃₀ + 1
                                                                   ==> i₁₂ < 100000))
                                                          && true
                                                          && (true
                                                             ==> true))
                                                      && (!(i₃₀ < 100000
                                                      )
                                                         ==> true
                                                          && (true
                                                             ==> true
                                                              && 0 <= 0
                                                              && 0 <= 100000
                                                              && (forall x₁₇: int ::
                                                                    ((exists i₁₆: int ::
                                                                            x₁₇ == i₁₆
                                                                            && 0 <= i₁₆
                                                                            && i₁₆ < 0)
                                                                       ==> (exists i₁₆: int ::
                                                                              i₁₆ < 100000
                                                                              && x₁₇ == i₁₆
                                                                              && 0 <= i₁₆
                                                                              && i₁₆ < 0
                                                                              && a3[x₁₇] == a2₂₉[i₁₆])))
                                                              && (forall x₁₇: int ::
                                                                    (!((exists i₁₆: int ::
                                                                            x₁₇ == i₁₆
                                                                            && 0 <= i₁₆
                                                                            && i₁₆ < 0)
                                                                    )
                                                                       ==> a3[x₁₇] == a3[x₁₇]))
                                                              && (forall i₁₆: int ::
                                                                    (  i₁₆ <= i₁₆
                                                                      && 0 <= i₁₆
                                                                      && i₁₆ < 0
                                                                       ==> i₁₆ < 100000))
                                                              && (forall a3₃₁: [int]int, i₃₂: int ::
                                                                    (  true
                                                                      && 0 <= i₃₂
                                                                      && i₃₂ <= 100000
                                                                      && (forall x₁₇: int ::
                                                                            ((exists i₁₆: int ::
                                                                                    x₁₇ == i₁₆
                                                                                    && 0 <= i₁₆
                                                                                    && i₁₆ < i₃₂)
                                                                               ==> (exists i₁₆: int ::
                                                                                      i₁₆ < 100000
                                                                                      && x₁₇ == i₁₆
                                                                                      && 0 <= i₁₆
                                                                                      && i₁₆ < i₃₂
                                                                                      && a3₃₁[x₁₇] == a2₂₉[i₁₆])))
                                                                      && (forall x₁₇: int ::
                                                                            (!((exists i₁₆: int ::
                                                                                    x₁₇ == i₁₆
                                                                                    && 0 <= i₁₆
                                                                                    && i₁₆ < i₃₂)
                                                                            )
                                                                               ==> a3₃₁[x₁₇] == a3[x₁₇]))
                                                                      && (forall i₁₆: int ::
                                                                            (  i₁₆ <= i₁₆
                                                                              && 0 <= i₁₆
                                                                              && i₁₆ < i₃₂
                                                                               ==> i₁₆ < 100000))
                                                                       ==> (i₃₂ < 100000
                                                                           ==> true
                                                                            && 0 <= i₃₂ + 1
                                                                            && i₃₂ + 1 <= 100000
                                                                            && (forall x₁₇: int ::
                                                                                  ((exists i₁₆: int ::
                                                                                          x₁₇ == i₁₆
                                                                                          && 0 <= i₁₆
                                                                                          && i₁₆ < i₃₂ + 1)
                                                                                     ==> (exists i₁₆: int ::
                                                                                            i₁₆ < 100000
                                                                                            && x₁₇ == i₁₆
                                                                                            && 0 <= i₁₆
                                                                                            && i₁₆ < i₃₂ + 1
                                                                                            && a3₃₁[i₃₂ := a2₂₉[i₃₂]][x₁₇] == a2₂₉[i₁₆])))
                                                                            && (forall x₁₇: int ::
                                                                                  (!((exists i₁₆: int ::
                                                                                          x₁₇ == i₁₆
                                                                                          && 0 <= i₁₆
                                                                                          && i₁₆ < i₃₂ + 1)
                                                                                  )
                                                                                     ==> a3₃₁[i₃₂ := a2₂₉[i₃₂]][x₁₇] == a3[x₁₇]))
                                                                            && (forall i₁₆: int ::
                                                                                  (  i₁₆ <= i₁₆
                                                                                    && 0 <= i₁₆
                                                                                    && i₁₆ < i₃₂ + 1
                                                                                     ==> i₁₆ < 100000))
                                                                            && true
                                                                            && (true
                                                                               ==> true))
                                                                        && (!(i₃₂ < 100000
                                                                        )
                                                                           ==> true
                                                                            && (true
                                                                               ==> true
                                                                                && 0 <= 0
                                                                                && 0 <= 100000
                                                                                && (forall x₂₁: int ::
                                                                                      ((exists i₂₀: int ::
                                                                                              x₂₁ == i₂₀
                                                                                              && 0 <= i₂₀
                                                                                              && i₂₀ < 0)
                                                                                         ==> (exists i₂₀: int ::
                                                                                                i₂₀ < 100000
                                                                                                && x₂₁ == i₂₀
                                                                                                && 0 <= i₂₀
                                                                                                && i₂₀ < 0
                                                                                                && a4[x₂₁] == a3₃₁[i₂₀])))
                                                                                && (forall x₂₁: int ::
                                                                                      (!((exists i₂₀: int ::
                                                                                              x₂₁ == i₂₀
                                                                                              && 0 <= i₂₀
                                                                                              && i₂₀ < 0)
                                                                                      )
                                                                                         ==> a4[x₂₁] == a4[x₂₁]))
                                                                                && (forall i₂₀: int ::
                                                                                      (  i₂₀ <= i₂₀
                                                                                        && 0 <= i₂₀
                                                                                        && i₂₀ < 0
                                                                                         ==> i₂₀ < 100000))
                                                                                && (forall a4₃₃: [int]int, i₃₄: int ::
                                                                                      (  true
                                                                                        && 0 <= i₃₄
                                                                                        && i₃₄ <= 100000
                                                                                        && (forall x₂₁: int ::
                                                                                              ((exists i₂₀: int ::
                                                                                                      x₂₁ == i₂₀
                                                                                                      && 0 <= i₂₀
                                                                                                      && i₂₀ < i₃₄)
                                                                                                 ==> (exists i₂₀: int ::
                                                                                                        i₂₀ < 100000
                                                                                                        && x₂₁ == i₂₀
                                                                                                        && 0 <= i₂₀
                                                                                                        && i₂₀ < i₃₄
                                                                                                        && a4₃₃[x₂₁] == a3₃₁[i₂₀])))
                                                                                        && (forall x₂₁: int ::
                                                                                              (!((exists i₂₀: int ::
                                                                                                      x₂₁ == i₂₀
                                                                                                      && 0 <= i₂₀
                                                                                                      && i₂₀ < i₃₄)
                                                                                              )
                                                                                                 ==> a4₃₃[x₂₁] == a4[x₂₁]))
                                                                                        && (forall i₂₀: int ::
                                                                                              (  i₂₀ <= i₂₀
                                                                                                && 0 <= i₂₀
                                                                                                && i₂₀ < i₃₄
                                                                                                 ==> i₂₀ < 100000))
                                                                                         ==> (i₃₄ < 100000
                                                                                             ==> true
                                                                                              && 0 <= i₃₄ + 1
                                                                                              && i₃₄ + 1 <= 100000
                                                                                              && (forall x₂₁: int ::
                                                                                                    ((exists i₂₀: int ::
                                                                                                            x₂₁ == i₂₀
                                                                                                            && 0 <= i₂₀
                                                                                                            && i₂₀ < i₃₄ + 1)
                                                                                                       ==> (exists i₂₀: int ::
                                                                                                              i₂₀ < 100000
                                                                                                              && x₂₁ == i₂₀
                                                                                                              && 0 <= i₂₀
                                                                                                              && i₂₀ < i₃₄ + 1
                                                                                                              && a4₃₃[i₃₄ := a3₃₁[i₃₄]][x₂₁] == a3₃₁[i₂₀])))
                                                                                              && (forall x₂₁: int ::
                                                                                                    (!((exists i₂₀: int ::
                                                                                                            x₂₁ == i₂₀
                                                                                                            && 0 <= i₂₀
                                                                                                            && i₂₀ < i₃₄ + 1)
                                                                                                    )
                                                                                                       ==> a4₃₃[i₃₄ := a3₃₁[i₃₄]][x₂₁] == a4[x₂₁]))
                                                                                              && (forall i₂₀: int ::
                                                                                                    (  i₂₀ <= i₂₀
                                                                                                      && 0 <= i₂₀
                                                                                                      && i₂₀ < i₃₄ + 1
                                                                                                       ==> i₂₀ < 100000))
                                                                                              && true
                                                                                              && (true
                                                                                                 ==> true))
                                                                                          && (!(i₃₄ < 100000
                                                                                          )
                                                                                             ==> true
                                                                                              && (true
                                                                                                 ==> true
                                                                                                  && 0 <= 0
                                                                                                  && 0 <= 100000
                                                                                                  && (forall x₂₅: int ::
                                                                                                        (  x₂₅ <= x₂₅
                                                                                                          && 0 <= x₂₅
                                                                                                          && x₂₅ < 0
                                                                                                           ==> x₂₅ < 100000))
                                                                                                  && (forall x₃₅: int ::
                                                                                                        (  true
                                                                                                          && 0 <= x₃₅
                                                                                                          && x₃₅ <= 100000
                                                                                                          && (forall x₂₅: int ::
                                                                                                                (  x₂₅ <= x₂₅
                                                                                                                  && 0 <= x₂₅
                                                                                                                  && x₂₅ < x₃₅
                                                                                                                   ==> x₂₅ < 100000))
                                                                                                           ==> (x₃₅ < 100000
                                                                                                               ==> a1₂₇[x₃₅] == a4₃₃[x₃₅]
                                                                                                                && (true
                                                                                                                   ==> true
                                                                                                                    && 0 <= x₃₅ + 1
                                                                                                                    && x₃₅ + 1 <= 100000
                                                                                                                    && (forall x₂₅: int ::
                                                                                                                          (  x₂₅ <= x₂₅
                                                                                                                            && 0 <= x₂₅
                                                                                                                            && x₂₅ < x₃₅ + 1
                                                                                                                             ==> x₂₅ < 100000))
                                                                                                                    && true
                                                                                                                    && (true
                                                                                                                       ==> true)))
                                                                                                            && (!(x₃₅ < 100000
                                                                                                            )
                                                                                                               ==> true
                                                                                                                && (true
                                                                                                                   ==> true))))))))))))))))))))))));


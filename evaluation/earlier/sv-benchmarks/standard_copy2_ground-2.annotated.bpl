data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int ::
      (forall a2: [int]int ::
            (forall a3: [int]int ::
                    true
                    && 0 <= 0
                    && 0 <= 100000
                    && (forall x₇: int ::
                          ((exists a₆: int ::
                                  x₇ == a₆
                                  && 0 <= a₆
                                  && a₆ < 0)
                             ==> (exists __VERIFIER_nondet_int₁₅: int, a₆: int ::
                                    a₆ < 100000
                                    && x₇ == a₆
                                    && 0 <= a₆
                                    && a₆ < 0
                                    && a1[x₇] == __VERIFIER_nondet_int₁₅)))
                    && (forall x₇: int ::
                          (!((exists a₆: int ::
                                  x₇ == a₆
                                  && 0 <= a₆
                                  && a₆ < 0)
                          )
                             ==> a1[x₇] == a1[x₇]))
                    && (forall a₆: int ::
                          (  a₆ <= a₆
                            && 0 <= a₆
                            && a₆ < 0
                             ==> a₆ < 100000))
                    && (forall a1₂₂: [int]int, a₂₃: int ::
                          (  true
                            && 0 <= a₂₃
                            && a₂₃ <= 100000
                            && (forall x₇: int ::
                                  ((exists a₆: int ::
                                          x₇ == a₆
                                          && 0 <= a₆
                                          && a₆ < a₂₃)
                                     ==> (exists __VERIFIER_nondet_int₁₅: int, a₆: int ::
                                            a₆ < 100000
                                            && x₇ == a₆
                                            && 0 <= a₆
                                            && a₆ < a₂₃
                                            && a1₂₂[x₇] == __VERIFIER_nondet_int₁₅)))
                            && (forall x₇: int ::
                                  (!((exists a₆: int ::
                                          x₇ == a₆
                                          && 0 <= a₆
                                          && a₆ < a₂₃)
                                  )
                                     ==> a1₂₂[x₇] == a1[x₇]))
                            && (forall a₆: int ::
                                  (  a₆ <= a₆
                                    && 0 <= a₆
                                    && a₆ < a₂₃
                                     ==> a₆ < 100000))
                             ==> (a₂₃ < 100000
                                 ==> (forall __VERIFIER_nondet_int₁: int ::
                                        true
                                        && 0 <= a₂₃ + 1
                                        && a₂₃ + 1 <= 100000
                                        && (forall x₇: int ::
                                              ((exists a₆: int ::
                                                      x₇ == a₆
                                                      && 0 <= a₆
                                                      && a₆ < a₂₃ + 1)
                                                 ==> (exists __VERIFIER_nondet_int₁₅: int, a₆: int ::
                                                        a₆ < 100000
                                                        && x₇ == a₆
                                                        && 0 <= a₆
                                                        && a₆ < a₂₃ + 1
                                                        && a1₂₂[a₂₃ := __VERIFIER_nondet_int₁][x₇] == __VERIFIER_nondet_int₁₅)))
                                        && (forall x₇: int ::
                                              (!((exists a₆: int ::
                                                      x₇ == a₆
                                                      && 0 <= a₆
                                                      && a₆ < a₂₃ + 1)
                                              )
                                                 ==> a1₂₂[a₂₃ := __VERIFIER_nondet_int₁][x₇] == a1[x₇]))
                                        && (forall a₆: int ::
                                              (  a₆ <= a₆
                                                && 0 <= a₆
                                                && a₆ < a₂₃ + 1
                                                 ==> a₆ < 100000))
                                        && true
                                        && (true
                                           ==> true)))
                              && (!(a₂₃ < 100000
                              )
                                 ==> true
                                  && (true
                                     ==> true
                                      && 0 <= 0
                                      && 0 <= 100000
                                      && (forall x₁₂: int ::
                                            ((exists i₁₁: int ::
                                                    x₁₂ == i₁₁
                                                    && 0 <= i₁₁
                                                    && i₁₁ < 0)
                                               ==> (exists i₁₁: int ::
                                                      i₁₁ < 100000
                                                      && x₁₂ == i₁₁
                                                      && 0 <= i₁₁
                                                      && i₁₁ < 0
                                                      && a2[x₁₂] == a1₂₂[i₁₁])))
                                      && (forall x₁₂: int ::
                                            (!((exists i₁₁: int ::
                                                    x₁₂ == i₁₁
                                                    && 0 <= i₁₁
                                                    && i₁₁ < 0)
                                            )
                                               ==> a2[x₁₂] == a2[x₁₂]))
                                      && (forall i₁₁: int ::
                                            (  i₁₁ <= i₁₁
                                              && 0 <= i₁₁
                                              && i₁₁ < 0
                                               ==> i₁₁ < 100000))
                                      && (forall a2₂₄: [int]int, i₂₅: int ::
                                            (  true
                                              && 0 <= i₂₅
                                              && i₂₅ <= 100000
                                              && (forall x₁₂: int ::
                                                    ((exists i₁₁: int ::
                                                            x₁₂ == i₁₁
                                                            && 0 <= i₁₁
                                                            && i₁₁ < i₂₅)
                                                       ==> (exists i₁₁: int ::
                                                              i₁₁ < 100000
                                                              && x₁₂ == i₁₁
                                                              && 0 <= i₁₁
                                                              && i₁₁ < i₂₅
                                                              && a2₂₄[x₁₂] == a1₂₂[i₁₁])))
                                              && (forall x₁₂: int ::
                                                    (!((exists i₁₁: int ::
                                                            x₁₂ == i₁₁
                                                            && 0 <= i₁₁
                                                            && i₁₁ < i₂₅)
                                                    )
                                                       ==> a2₂₄[x₁₂] == a2[x₁₂]))
                                              && (forall i₁₁: int ::
                                                    (  i₁₁ <= i₁₁
                                                      && 0 <= i₁₁
                                                      && i₁₁ < i₂₅
                                                       ==> i₁₁ < 100000))
                                               ==> (i₂₅ < 100000
                                                   ==> true
                                                    && 0 <= i₂₅ + 1
                                                    && i₂₅ + 1 <= 100000
                                                    && (forall x₁₂: int ::
                                                          ((exists i₁₁: int ::
                                                                  x₁₂ == i₁₁
                                                                  && 0 <= i₁₁
                                                                  && i₁₁ < i₂₅ + 1)
                                                             ==> (exists i₁₁: int ::
                                                                    i₁₁ < 100000
                                                                    && x₁₂ == i₁₁
                                                                    && 0 <= i₁₁
                                                                    && i₁₁ < i₂₅ + 1
                                                                    && a2₂₄[i₂₅ := a1₂₂[i₂₅]][x₁₂] == a1₂₂[i₁₁])))
                                                    && (forall x₁₂: int ::
                                                          (!((exists i₁₁: int ::
                                                                  x₁₂ == i₁₁
                                                                  && 0 <= i₁₁
                                                                  && i₁₁ < i₂₅ + 1)
                                                          )
                                                             ==> a2₂₄[i₂₅ := a1₂₂[i₂₅]][x₁₂] == a2[x₁₂]))
                                                    && (forall i₁₁: int ::
                                                          (  i₁₁ <= i₁₁
                                                            && 0 <= i₁₁
                                                            && i₁₁ < i₂₅ + 1
                                                             ==> i₁₁ < 100000))
                                                    && true
                                                    && (true
                                                       ==> true))
                                                && (!(i₂₅ < 100000
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> true
                                                        && 0 <= 0
                                                        && 0 <= 100000
                                                        && (forall x₁₆: int ::
                                                              ((exists i₁₅: int ::
                                                                      x₁₆ == i₁₅
                                                                      && 0 <= i₁₅
                                                                      && i₁₅ < 0)
                                                                 ==> (exists i₁₅: int ::
                                                                        i₁₅ < 100000
                                                                        && x₁₆ == i₁₅
                                                                        && 0 <= i₁₅
                                                                        && i₁₅ < 0
                                                                        && a3[x₁₆] == a2₂₄[i₁₅])))
                                                        && (forall x₁₆: int ::
                                                              (!((exists i₁₅: int ::
                                                                      x₁₆ == i₁₅
                                                                      && 0 <= i₁₅
                                                                      && i₁₅ < 0)
                                                              )
                                                                 ==> a3[x₁₆] == a3[x₁₆]))
                                                        && (forall i₁₅: int ::
                                                              (  i₁₅ <= i₁₅
                                                                && 0 <= i₁₅
                                                                && i₁₅ < 0
                                                                 ==> i₁₅ < 100000))
                                                        && (forall a3₂₆: [int]int, i₂₇: int ::
                                                              (  true
                                                                && 0 <= i₂₇
                                                                && i₂₇ <= 100000
                                                                && (forall x₁₆: int ::
                                                                      ((exists i₁₅: int ::
                                                                              x₁₆ == i₁₅
                                                                              && 0 <= i₁₅
                                                                              && i₁₅ < i₂₇)
                                                                         ==> (exists i₁₅: int ::
                                                                                i₁₅ < 100000
                                                                                && x₁₆ == i₁₅
                                                                                && 0 <= i₁₅
                                                                                && i₁₅ < i₂₇
                                                                                && a3₂₆[x₁₆] == a2₂₄[i₁₅])))
                                                                && (forall x₁₆: int ::
                                                                      (!((exists i₁₅: int ::
                                                                              x₁₆ == i₁₅
                                                                              && 0 <= i₁₅
                                                                              && i₁₅ < i₂₇)
                                                                      )
                                                                         ==> a3₂₆[x₁₆] == a3[x₁₆]))
                                                                && (forall i₁₅: int ::
                                                                      (  i₁₅ <= i₁₅
                                                                        && 0 <= i₁₅
                                                                        && i₁₅ < i₂₇
                                                                         ==> i₁₅ < 100000))
                                                                 ==> (i₂₇ < 100000
                                                                     ==> true
                                                                      && 0 <= i₂₇ + 1
                                                                      && i₂₇ + 1 <= 100000
                                                                      && (forall x₁₆: int ::
                                                                            ((exists i₁₅: int ::
                                                                                    x₁₆ == i₁₅
                                                                                    && 0 <= i₁₅
                                                                                    && i₁₅ < i₂₇ + 1)
                                                                               ==> (exists i₁₅: int ::
                                                                                      i₁₅ < 100000
                                                                                      && x₁₆ == i₁₅
                                                                                      && 0 <= i₁₅
                                                                                      && i₁₅ < i₂₇ + 1
                                                                                      && a3₂₆[i₂₇ := a2₂₄[i₂₇]][x₁₆] == a2₂₄[i₁₅])))
                                                                      && (forall x₁₆: int ::
                                                                            (!((exists i₁₅: int ::
                                                                                    x₁₆ == i₁₅
                                                                                    && 0 <= i₁₅
                                                                                    && i₁₅ < i₂₇ + 1)
                                                                            )
                                                                               ==> a3₂₆[i₂₇ := a2₂₄[i₂₇]][x₁₆] == a3[x₁₆]))
                                                                      && (forall i₁₅: int ::
                                                                            (  i₁₅ <= i₁₅
                                                                              && 0 <= i₁₅
                                                                              && i₁₅ < i₂₇ + 1
                                                                               ==> i₁₅ < 100000))
                                                                      && true
                                                                      && (true
                                                                         ==> true))
                                                                  && (!(i₂₇ < 100000
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true
                                                                          && 0 <= 0
                                                                          && 0 <= 100000
                                                                          && (forall x₂₀: int ::
                                                                                (  x₂₀ <= x₂₀
                                                                                  && 0 <= x₂₀
                                                                                  && x₂₀ < 0
                                                                                   ==> x₂₀ < 100000))
                                                                          && (forall x₂₈: int ::
                                                                                (  true
                                                                                  && 0 <= x₂₈
                                                                                  && x₂₈ <= 100000
                                                                                  && (forall x₂₀: int ::
                                                                                        (  x₂₀ <= x₂₀
                                                                                          && 0 <= x₂₀
                                                                                          && x₂₀ < x₂₈
                                                                                           ==> x₂₀ < 100000))
                                                                                   ==> (x₂₈ < 100000
                                                                                       ==> a1₂₂[x₂₈] == a3₂₆[x₂₈]
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 0 <= x₂₈ + 1
                                                                                            && x₂₈ + 1 <= 100000
                                                                                            && (forall x₂₀: int ::
                                                                                                  (  x₂₀ <= x₂₀
                                                                                                    && 0 <= x₂₀
                                                                                                    && x₂₀ < x₂₈ + 1
                                                                                                     ==> x₂₀ < 100000))
                                                                                            && true
                                                                                            && (true
                                                                                               ==> true)))
                                                                                    && (!(x₂₈ < 100000
                                                                                    )
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true)))))))))))))))))));


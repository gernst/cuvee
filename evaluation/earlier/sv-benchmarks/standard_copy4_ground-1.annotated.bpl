data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int ::
      (forall a2: [int]int ::
            (forall a3: [int]int ::
                  (forall a4: [int]int ::
                        (forall a5: [int]int ::
                                true
                                && 0 <= 0
                                && 0 <= 100000
                                && (forall x₉: int ::
                                      ((exists a₈: int ::
                                              x₉ == a₈
                                              && 0 <= a₈
                                              && a₈ < 0)
                                         ==> (exists __VERIFIER_nondet_int₁₇: int, a₈: int ::
                                                a₈ < 100000
                                                && x₉ == a₈
                                                && 0 <= a₈
                                                && a₈ < 0
                                                && a1[x₉] == __VERIFIER_nondet_int₁₇)))
                                && (forall x₉: int ::
                                      (!((exists a₈: int ::
                                              x₉ == a₈
                                              && 0 <= a₈
                                              && a₈ < 0)
                                      )
                                         ==> a1[x₉] == a1[x₉]))
                                && (forall a₈: int ::
                                      (  a₈ <= a₈
                                        && 0 <= a₈
                                        && a₈ < 0
                                         ==> a₈ < 100000))
                                && (forall a1₃₂: [int]int, a₃₃: int ::
                                      (  true
                                        && 0 <= a₃₃
                                        && a₃₃ <= 100000
                                        && (forall x₉: int ::
                                              ((exists a₈: int ::
                                                      x₉ == a₈
                                                      && 0 <= a₈
                                                      && a₈ < a₃₃)
                                                 ==> (exists __VERIFIER_nondet_int₁₇: int, a₈: int ::
                                                        a₈ < 100000
                                                        && x₉ == a₈
                                                        && 0 <= a₈
                                                        && a₈ < a₃₃
                                                        && a1₃₂[x₉] == __VERIFIER_nondet_int₁₇)))
                                        && (forall x₉: int ::
                                              (!((exists a₈: int ::
                                                      x₉ == a₈
                                                      && 0 <= a₈
                                                      && a₈ < a₃₃)
                                              )
                                                 ==> a1₃₂[x₉] == a1[x₉]))
                                        && (forall a₈: int ::
                                              (  a₈ <= a₈
                                                && 0 <= a₈
                                                && a₈ < a₃₃
                                                 ==> a₈ < 100000))
                                         ==> (a₃₃ < 100000
                                             ==> (forall __VERIFIER_nondet_int₁: int ::
                                                    true
                                                    && 0 <= a₃₃ + 1
                                                    && a₃₃ + 1 <= 100000
                                                    && (forall x₉: int ::
                                                          ((exists a₈: int ::
                                                                  x₉ == a₈
                                                                  && 0 <= a₈
                                                                  && a₈ < a₃₃ + 1)
                                                             ==> (exists __VERIFIER_nondet_int₁₇: int, a₈: int ::
                                                                    a₈ < 100000
                                                                    && x₉ == a₈
                                                                    && 0 <= a₈
                                                                    && a₈ < a₃₃ + 1
                                                                    && a1₃₂[a₃₃ := __VERIFIER_nondet_int₁][x₉] == __VERIFIER_nondet_int₁₇)))
                                                    && (forall x₉: int ::
                                                          (!((exists a₈: int ::
                                                                  x₉ == a₈
                                                                  && 0 <= a₈
                                                                  && a₈ < a₃₃ + 1)
                                                          )
                                                             ==> a1₃₂[a₃₃ := __VERIFIER_nondet_int₁][x₉] == a1[x₉]))
                                                    && (forall a₈: int ::
                                                          (  a₈ <= a₈
                                                            && 0 <= a₈
                                                            && a₈ < a₃₃ + 1
                                                             ==> a₈ < 100000))
                                                    && true
                                                    && (true
                                                       ==> true)))
                                          && (!(a₃₃ < 100000
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₁₄: int ::
                                                        ((exists i₁₃: int ::
                                                                x₁₄ == i₁₃
                                                                && 0 <= i₁₃
                                                                && i₁₃ < 0)
                                                           ==> (exists i₁₃: int ::
                                                                  i₁₃ < 100000
                                                                  && x₁₄ == i₁₃
                                                                  && 0 <= i₁₃
                                                                  && i₁₃ < 0
                                                                  && a2[x₁₄] == a1₃₂[i₁₃])))
                                                  && (forall x₁₄: int ::
                                                        (!((exists i₁₃: int ::
                                                                x₁₄ == i₁₃
                                                                && 0 <= i₁₃
                                                                && i₁₃ < 0)
                                                        )
                                                           ==> a2[x₁₄] == a2[x₁₄]))
                                                  && (forall i₁₃: int ::
                                                        (  i₁₃ <= i₁₃
                                                          && 0 <= i₁₃
                                                          && i₁₃ < 0
                                                           ==> i₁₃ < 100000))
                                                  && (forall a2₃₄: [int]int, i₃₅: int ::
                                                        (  true
                                                          && 0 <= i₃₅
                                                          && i₃₅ <= 100000
                                                          && (forall x₁₄: int ::
                                                                ((exists i₁₃: int ::
                                                                        x₁₄ == i₁₃
                                                                        && 0 <= i₁₃
                                                                        && i₁₃ < i₃₅)
                                                                   ==> (exists i₁₃: int ::
                                                                          i₁₃ < 100000
                                                                          && x₁₄ == i₁₃
                                                                          && 0 <= i₁₃
                                                                          && i₁₃ < i₃₅
                                                                          && a2₃₄[x₁₄] == a1₃₂[i₁₃])))
                                                          && (forall x₁₄: int ::
                                                                (!((exists i₁₃: int ::
                                                                        x₁₄ == i₁₃
                                                                        && 0 <= i₁₃
                                                                        && i₁₃ < i₃₅)
                                                                )
                                                                   ==> a2₃₄[x₁₄] == a2[x₁₄]))
                                                          && (forall i₁₃: int ::
                                                                (  i₁₃ <= i₁₃
                                                                  && 0 <= i₁₃
                                                                  && i₁₃ < i₃₅
                                                                   ==> i₁₃ < 100000))
                                                           ==> (i₃₅ < 100000
                                                               ==> true
                                                                && 0 <= i₃₅ + 1
                                                                && i₃₅ + 1 <= 100000
                                                                && (forall x₁₄: int ::
                                                                      ((exists i₁₃: int ::
                                                                              x₁₄ == i₁₃
                                                                              && 0 <= i₁₃
                                                                              && i₁₃ < i₃₅ + 1)
                                                                         ==> (exists i₁₃: int ::
                                                                                i₁₃ < 100000
                                                                                && x₁₄ == i₁₃
                                                                                && 0 <= i₁₃
                                                                                && i₁₃ < i₃₅ + 1
                                                                                && a2₃₄[i₃₅ := a1₃₂[i₃₅]][x₁₄] == a1₃₂[i₁₃])))
                                                                && (forall x₁₄: int ::
                                                                      (!((exists i₁₃: int ::
                                                                              x₁₄ == i₁₃
                                                                              && 0 <= i₁₃
                                                                              && i₁₃ < i₃₅ + 1)
                                                                      )
                                                                         ==> a2₃₄[i₃₅ := a1₃₂[i₃₅]][x₁₄] == a2[x₁₄]))
                                                                && (forall i₁₃: int ::
                                                                      (  i₁₃ <= i₁₃
                                                                        && 0 <= i₁₃
                                                                        && i₁₃ < i₃₅ + 1
                                                                         ==> i₁₃ < 100000))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (!(i₃₅ < 100000
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= 0
                                                                    && 0 <= 100000
                                                                    && (forall x₁₈: int ::
                                                                          ((exists i₁₇: int ::
                                                                                  x₁₈ == i₁₇
                                                                                  && 0 <= i₁₇
                                                                                  && i₁₇ < 0)
                                                                             ==> (exists i₁₇: int ::
                                                                                    i₁₇ < 100000
                                                                                    && x₁₈ == i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < 0
                                                                                    && a3[x₁₈] == a2₃₄[i₁₇])))
                                                                    && (forall x₁₈: int ::
                                                                          (!((exists i₁₇: int ::
                                                                                  x₁₈ == i₁₇
                                                                                  && 0 <= i₁₇
                                                                                  && i₁₇ < 0)
                                                                          )
                                                                             ==> a3[x₁₈] == a3[x₁₈]))
                                                                    && (forall i₁₇: int ::
                                                                          (  i₁₇ <= i₁₇
                                                                            && 0 <= i₁₇
                                                                            && i₁₇ < 0
                                                                             ==> i₁₇ < 100000))
                                                                    && (forall a3₃₆: [int]int, i₃₇: int ::
                                                                          (  true
                                                                            && 0 <= i₃₇
                                                                            && i₃₇ <= 100000
                                                                            && (forall x₁₈: int ::
                                                                                  ((exists i₁₇: int ::
                                                                                          x₁₈ == i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₃₇)
                                                                                     ==> (exists i₁₇: int ::
                                                                                            i₁₇ < 100000
                                                                                            && x₁₈ == i₁₇
                                                                                            && 0 <= i₁₇
                                                                                            && i₁₇ < i₃₇
                                                                                            && a3₃₆[x₁₈] == a2₃₄[i₁₇])))
                                                                            && (forall x₁₈: int ::
                                                                                  (!((exists i₁₇: int ::
                                                                                          x₁₈ == i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₃₇)
                                                                                  )
                                                                                     ==> a3₃₆[x₁₈] == a3[x₁₈]))
                                                                            && (forall i₁₇: int ::
                                                                                  (  i₁₇ <= i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < i₃₇
                                                                                     ==> i₁₇ < 100000))
                                                                             ==> (i₃₇ < 100000
                                                                                 ==> true
                                                                                  && 0 <= i₃₇ + 1
                                                                                  && i₃₇ + 1 <= 100000
                                                                                  && (forall x₁₈: int ::
                                                                                        ((exists i₁₇: int ::
                                                                                                x₁₈ == i₁₇
                                                                                                && 0 <= i₁₇
                                                                                                && i₁₇ < i₃₇ + 1)
                                                                                           ==> (exists i₁₇: int ::
                                                                                                  i₁₇ < 100000
                                                                                                  && x₁₈ == i₁₇
                                                                                                  && 0 <= i₁₇
                                                                                                  && i₁₇ < i₃₇ + 1
                                                                                                  && a3₃₆[i₃₇ := a2₃₄[i₃₇]][x₁₈] == a2₃₄[i₁₇])))
                                                                                  && (forall x₁₈: int ::
                                                                                        (!((exists i₁₇: int ::
                                                                                                x₁₈ == i₁₇
                                                                                                && 0 <= i₁₇
                                                                                                && i₁₇ < i₃₇ + 1)
                                                                                        )
                                                                                           ==> a3₃₆[i₃₇ := a2₃₄[i₃₇]][x₁₈] == a3[x₁₈]))
                                                                                  && (forall i₁₇: int ::
                                                                                        (  i₁₇ <= i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₃₇ + 1
                                                                                           ==> i₁₇ < 100000))
                                                                                  && true
                                                                                  && (true
                                                                                     ==> true))
                                                                              && (!(i₃₇ < 100000
                                                                              )
                                                                                 ==> true
                                                                                  && (true
                                                                                     ==> true
                                                                                      && 0 <= 0
                                                                                      && 0 <= 100000
                                                                                      && (forall x₂₂: int ::
                                                                                            ((exists i₂₁: int ::
                                                                                                    x₂₂ == i₂₁
                                                                                                    && 0 <= i₂₁
                                                                                                    && i₂₁ < 0)
                                                                                               ==> (exists i₂₁: int ::
                                                                                                      i₂₁ < 100000
                                                                                                      && x₂₂ == i₂₁
                                                                                                      && 0 <= i₂₁
                                                                                                      && i₂₁ < 0
                                                                                                      && a4[x₂₂] == a3₃₆[i₂₁])))
                                                                                      && (forall x₂₂: int ::
                                                                                            (!((exists i₂₁: int ::
                                                                                                    x₂₂ == i₂₁
                                                                                                    && 0 <= i₂₁
                                                                                                    && i₂₁ < 0)
                                                                                            )
                                                                                               ==> a4[x₂₂] == a4[x₂₂]))
                                                                                      && (forall i₂₁: int ::
                                                                                            (  i₂₁ <= i₂₁
                                                                                              && 0 <= i₂₁
                                                                                              && i₂₁ < 0
                                                                                               ==> i₂₁ < 100000))
                                                                                      && (forall a4₃₈: [int]int, i₃₉: int ::
                                                                                            (  true
                                                                                              && 0 <= i₃₉
                                                                                              && i₃₉ <= 100000
                                                                                              && (forall x₂₂: int ::
                                                                                                    ((exists i₂₁: int ::
                                                                                                            x₂₂ == i₂₁
                                                                                                            && 0 <= i₂₁
                                                                                                            && i₂₁ < i₃₉)
                                                                                                       ==> (exists i₂₁: int ::
                                                                                                              i₂₁ < 100000
                                                                                                              && x₂₂ == i₂₁
                                                                                                              && 0 <= i₂₁
                                                                                                              && i₂₁ < i₃₉
                                                                                                              && a4₃₈[x₂₂] == a3₃₆[i₂₁])))
                                                                                              && (forall x₂₂: int ::
                                                                                                    (!((exists i₂₁: int ::
                                                                                                            x₂₂ == i₂₁
                                                                                                            && 0 <= i₂₁
                                                                                                            && i₂₁ < i₃₉)
                                                                                                    )
                                                                                                       ==> a4₃₈[x₂₂] == a4[x₂₂]))
                                                                                              && (forall i₂₁: int ::
                                                                                                    (  i₂₁ <= i₂₁
                                                                                                      && 0 <= i₂₁
                                                                                                      && i₂₁ < i₃₉
                                                                                                       ==> i₂₁ < 100000))
                                                                                               ==> (i₃₉ < 100000
                                                                                                   ==> true
                                                                                                    && 0 <= i₃₉ + 1
                                                                                                    && i₃₉ + 1 <= 100000
                                                                                                    && (forall x₂₂: int ::
                                                                                                          ((exists i₂₁: int ::
                                                                                                                  x₂₂ == i₂₁
                                                                                                                  && 0 <= i₂₁
                                                                                                                  && i₂₁ < i₃₉ + 1)
                                                                                                             ==> (exists i₂₁: int ::
                                                                                                                    i₂₁ < 100000
                                                                                                                    && x₂₂ == i₂₁
                                                                                                                    && 0 <= i₂₁
                                                                                                                    && i₂₁ < i₃₉ + 1
                                                                                                                    && a4₃₈[i₃₉ := a3₃₆[i₃₉]][x₂₂] == a3₃₆[i₂₁])))
                                                                                                    && (forall x₂₂: int ::
                                                                                                          (!((exists i₂₁: int ::
                                                                                                                  x₂₂ == i₂₁
                                                                                                                  && 0 <= i₂₁
                                                                                                                  && i₂₁ < i₃₉ + 1)
                                                                                                          )
                                                                                                             ==> a4₃₈[i₃₉ := a3₃₆[i₃₉]][x₂₂] == a4[x₂₂]))
                                                                                                    && (forall i₂₁: int ::
                                                                                                          (  i₂₁ <= i₂₁
                                                                                                            && 0 <= i₂₁
                                                                                                            && i₂₁ < i₃₉ + 1
                                                                                                             ==> i₂₁ < 100000))
                                                                                                    && true
                                                                                                    && (true
                                                                                                       ==> true))
                                                                                                && (!(i₃₉ < 100000
                                                                                                )
                                                                                                   ==> true
                                                                                                    && (true
                                                                                                       ==> true
                                                                                                        && 0 <= 0
                                                                                                        && 0 <= 100000
                                                                                                        && (forall x₂₆: int ::
                                                                                                              ((exists i₂₅: int ::
                                                                                                                      x₂₆ == i₂₅
                                                                                                                      && 0 <= i₂₅
                                                                                                                      && i₂₅ < 0)
                                                                                                                 ==> (exists i₂₅: int ::
                                                                                                                        i₂₅ < 100000
                                                                                                                        && x₂₆ == i₂₅
                                                                                                                        && 0 <= i₂₅
                                                                                                                        && i₂₅ < 0
                                                                                                                        && a5[x₂₆] == a4₃₈[i₂₅])))
                                                                                                        && (forall x₂₆: int ::
                                                                                                              (!((exists i₂₅: int ::
                                                                                                                      x₂₆ == i₂₅
                                                                                                                      && 0 <= i₂₅
                                                                                                                      && i₂₅ < 0)
                                                                                                              )
                                                                                                                 ==> a5[x₂₆] == a5[x₂₆]))
                                                                                                        && (forall i₂₅: int ::
                                                                                                              (  i₂₅ <= i₂₅
                                                                                                                && 0 <= i₂₅
                                                                                                                && i₂₅ < 0
                                                                                                                 ==> i₂₅ < 100000))
                                                                                                        && (forall a5₄₀: [int]int, i₄₁: int ::
                                                                                                              (  true
                                                                                                                && 0 <= i₄₁
                                                                                                                && i₄₁ <= 100000
                                                                                                                && (forall x₂₆: int ::
                                                                                                                      ((exists i₂₅: int ::
                                                                                                                              x₂₆ == i₂₅
                                                                                                                              && 0 <= i₂₅
                                                                                                                              && i₂₅ < i₄₁)
                                                                                                                         ==> (exists i₂₅: int ::
                                                                                                                                i₂₅ < 100000
                                                                                                                                && x₂₆ == i₂₅
                                                                                                                                && 0 <= i₂₅
                                                                                                                                && i₂₅ < i₄₁
                                                                                                                                && a5₄₀[x₂₆] == a4₃₈[i₂₅])))
                                                                                                                && (forall x₂₆: int ::
                                                                                                                      (!((exists i₂₅: int ::
                                                                                                                              x₂₆ == i₂₅
                                                                                                                              && 0 <= i₂₅
                                                                                                                              && i₂₅ < i₄₁)
                                                                                                                      )
                                                                                                                         ==> a5₄₀[x₂₆] == a5[x₂₆]))
                                                                                                                && (forall i₂₅: int ::
                                                                                                                      (  i₂₅ <= i₂₅
                                                                                                                        && 0 <= i₂₅
                                                                                                                        && i₂₅ < i₄₁
                                                                                                                         ==> i₂₅ < 100000))
                                                                                                                 ==> (i₄₁ < 100000
                                                                                                                     ==> true
                                                                                                                      && 0 <= i₄₁ + 1
                                                                                                                      && i₄₁ + 1 <= 100000
                                                                                                                      && (forall x₂₆: int ::
                                                                                                                            ((exists i₂₅: int ::
                                                                                                                                    x₂₆ == i₂₅
                                                                                                                                    && 0 <= i₂₅
                                                                                                                                    && i₂₅ < i₄₁ + 1)
                                                                                                                               ==> (exists i₂₅: int ::
                                                                                                                                      i₂₅ < 100000
                                                                                                                                      && x₂₆ == i₂₅
                                                                                                                                      && 0 <= i₂₅
                                                                                                                                      && i₂₅ < i₄₁ + 1
                                                                                                                                      && a5₄₀[i₄₁ := a4₃₈[i₄₁]][x₂₆] == a4₃₈[i₂₅])))
                                                                                                                      && (forall x₂₆: int ::
                                                                                                                            (!((exists i₂₅: int ::
                                                                                                                                    x₂₆ == i₂₅
                                                                                                                                    && 0 <= i₂₅
                                                                                                                                    && i₂₅ < i₄₁ + 1)
                                                                                                                            )
                                                                                                                               ==> a5₄₀[i₄₁ := a4₃₈[i₄₁]][x₂₆] == a5[x₂₆]))
                                                                                                                      && (forall i₂₅: int ::
                                                                                                                            (  i₂₅ <= i₂₅
                                                                                                                              && 0 <= i₂₅
                                                                                                                              && i₂₅ < i₄₁ + 1
                                                                                                                               ==> i₂₅ < 100000))
                                                                                                                      && true
                                                                                                                      && (true
                                                                                                                         ==> true))
                                                                                                                  && (!(i₄₁ < 100000
                                                                                                                  )
                                                                                                                     ==> true
                                                                                                                      && (true
                                                                                                                         ==> true
                                                                                                                          && 0 <= 0
                                                                                                                          && 0 <= 100000
                                                                                                                          && (forall x₃₀: int ::
                                                                                                                                (  x₃₀ <= x₃₀
                                                                                                                                  && 0 <= x₃₀
                                                                                                                                  && x₃₀ < 0
                                                                                                                                   ==> x₃₀ < 100000))
                                                                                                                          && (forall x₄₂: int ::
                                                                                                                                (  true
                                                                                                                                  && 0 <= x₄₂
                                                                                                                                  && x₄₂ <= 100000
                                                                                                                                  && (forall x₃₀: int ::
                                                                                                                                        (  x₃₀ <= x₃₀
                                                                                                                                          && 0 <= x₃₀
                                                                                                                                          && x₃₀ < x₄₂
                                                                                                                                           ==> x₃₀ < 100000))
                                                                                                                                   ==> (x₄₂ < 100000
                                                                                                                                       ==> a1₃₂[x₄₂] == a5₄₀[x₄₂]
                                                                                                                                        && (true
                                                                                                                                           ==> true
                                                                                                                                            && 0 <= x₄₂ + 1
                                                                                                                                            && x₄₂ + 1 <= 100000
                                                                                                                                            && (forall x₃₀: int ::
                                                                                                                                                  (  x₃₀ <= x₃₀
                                                                                                                                                    && 0 <= x₃₀
                                                                                                                                                    && x₃₀ < x₄₂ + 1
                                                                                                                                                     ==> x₃₀ < 100000))
                                                                                                                                            && true
                                                                                                                                            && (true
                                                                                                                                               ==> true)))
                                                                                                                                    && (!(x₄₂ < 100000
                                                                                                                                    )
                                                                                                                                       ==> true
                                                                                                                                        && (true
                                                                                                                                           ==> true)))))))))))))))))))))))))))));


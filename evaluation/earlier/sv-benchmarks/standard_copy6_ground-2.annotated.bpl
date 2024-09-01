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
                              (forall a6: [int]int ::
                                    (forall a7: [int]int ::
                                            true
                                            && 0 <= 0
                                            && 0 <= 100000
                                            && (forall x₁₁: int ::
                                                  ((exists a₁₀: int ::
                                                          x₁₁ == a₁₀
                                                          && 0 <= a₁₀
                                                          && a₁₀ < 0)
                                                     ==> (exists __VERIFIER_nondet_int₁₉: int, a₁₀: int ::
                                                            a₁₀ < 100000
                                                            && x₁₁ == a₁₀
                                                            && 0 <= a₁₀
                                                            && a₁₀ < 0
                                                            && a1[x₁₁] == __VERIFIER_nondet_int₁₉)))
                                            && (forall x₁₁: int ::
                                                  (!((exists a₁₀: int ::
                                                          x₁₁ == a₁₀
                                                          && 0 <= a₁₀
                                                          && a₁₀ < 0)
                                                  )
                                                     ==> a1[x₁₁] == a1[x₁₁]))
                                            && (forall a₁₀: int ::
                                                  (  a₁₀ <= a₁₀
                                                    && 0 <= a₁₀
                                                    && a₁₀ < 0
                                                     ==> a₁₀ < 100000))
                                            && (forall a1₄₂: [int]int, a₄₃: int ::
                                                  (  true
                                                    && 0 <= a₄₃
                                                    && a₄₃ <= 100000
                                                    && (forall x₁₁: int ::
                                                          ((exists a₁₀: int ::
                                                                  x₁₁ == a₁₀
                                                                  && 0 <= a₁₀
                                                                  && a₁₀ < a₄₃)
                                                             ==> (exists __VERIFIER_nondet_int₁₉: int, a₁₀: int ::
                                                                    a₁₀ < 100000
                                                                    && x₁₁ == a₁₀
                                                                    && 0 <= a₁₀
                                                                    && a₁₀ < a₄₃
                                                                    && a1₄₂[x₁₁] == __VERIFIER_nondet_int₁₉)))
                                                    && (forall x₁₁: int ::
                                                          (!((exists a₁₀: int ::
                                                                  x₁₁ == a₁₀
                                                                  && 0 <= a₁₀
                                                                  && a₁₀ < a₄₃)
                                                          )
                                                             ==> a1₄₂[x₁₁] == a1[x₁₁]))
                                                    && (forall a₁₀: int ::
                                                          (  a₁₀ <= a₁₀
                                                            && 0 <= a₁₀
                                                            && a₁₀ < a₄₃
                                                             ==> a₁₀ < 100000))
                                                     ==> (a₄₃ < 100000
                                                         ==> (forall __VERIFIER_nondet_int₁: int ::
                                                                true
                                                                && 0 <= a₄₃ + 1
                                                                && a₄₃ + 1 <= 100000
                                                                && (forall x₁₁: int ::
                                                                      ((exists a₁₀: int ::
                                                                              x₁₁ == a₁₀
                                                                              && 0 <= a₁₀
                                                                              && a₁₀ < a₄₃ + 1)
                                                                         ==> (exists __VERIFIER_nondet_int₁₉: int, a₁₀: int ::
                                                                                a₁₀ < 100000
                                                                                && x₁₁ == a₁₀
                                                                                && 0 <= a₁₀
                                                                                && a₁₀ < a₄₃ + 1
                                                                                && a1₄₂[a₄₃ := __VERIFIER_nondet_int₁][x₁₁] == __VERIFIER_nondet_int₁₉)))
                                                                && (forall x₁₁: int ::
                                                                      (!((exists a₁₀: int ::
                                                                              x₁₁ == a₁₀
                                                                              && 0 <= a₁₀
                                                                              && a₁₀ < a₄₃ + 1)
                                                                      )
                                                                         ==> a1₄₂[a₄₃ := __VERIFIER_nondet_int₁][x₁₁] == a1[x₁₁]))
                                                                && (forall a₁₀: int ::
                                                                      (  a₁₀ <= a₁₀
                                                                        && 0 <= a₁₀
                                                                        && a₁₀ < a₄₃ + 1
                                                                         ==> a₁₀ < 100000))
                                                                && true
                                                                && (true
                                                                   ==> true)))
                                                      && (!(a₄₃ < 100000
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
                                                                              && a2[x₁₆] == a1₄₂[i₁₅])))
                                                              && (forall x₁₆: int ::
                                                                    (!((exists i₁₅: int ::
                                                                            x₁₆ == i₁₅
                                                                            && 0 <= i₁₅
                                                                            && i₁₅ < 0)
                                                                    )
                                                                       ==> a2[x₁₆] == a2[x₁₆]))
                                                              && (forall i₁₅: int ::
                                                                    (  i₁₅ <= i₁₅
                                                                      && 0 <= i₁₅
                                                                      && i₁₅ < 0
                                                                       ==> i₁₅ < 100000))
                                                              && (forall a2₄₄: [int]int, i₄₅: int ::
                                                                    (  true
                                                                      && 0 <= i₄₅
                                                                      && i₄₅ <= 100000
                                                                      && (forall x₁₆: int ::
                                                                            ((exists i₁₅: int ::
                                                                                    x₁₆ == i₁₅
                                                                                    && 0 <= i₁₅
                                                                                    && i₁₅ < i₄₅)
                                                                               ==> (exists i₁₅: int ::
                                                                                      i₁₅ < 100000
                                                                                      && x₁₆ == i₁₅
                                                                                      && 0 <= i₁₅
                                                                                      && i₁₅ < i₄₅
                                                                                      && a2₄₄[x₁₆] == a1₄₂[i₁₅])))
                                                                      && (forall x₁₆: int ::
                                                                            (!((exists i₁₅: int ::
                                                                                    x₁₆ == i₁₅
                                                                                    && 0 <= i₁₅
                                                                                    && i₁₅ < i₄₅)
                                                                            )
                                                                               ==> a2₄₄[x₁₆] == a2[x₁₆]))
                                                                      && (forall i₁₅: int ::
                                                                            (  i₁₅ <= i₁₅
                                                                              && 0 <= i₁₅
                                                                              && i₁₅ < i₄₅
                                                                               ==> i₁₅ < 100000))
                                                                       ==> (i₄₅ < 100000
                                                                           ==> true
                                                                            && 0 <= i₄₅ + 1
                                                                            && i₄₅ + 1 <= 100000
                                                                            && (forall x₁₆: int ::
                                                                                  ((exists i₁₅: int ::
                                                                                          x₁₆ == i₁₅
                                                                                          && 0 <= i₁₅
                                                                                          && i₁₅ < i₄₅ + 1)
                                                                                     ==> (exists i₁₅: int ::
                                                                                            i₁₅ < 100000
                                                                                            && x₁₆ == i₁₅
                                                                                            && 0 <= i₁₅
                                                                                            && i₁₅ < i₄₅ + 1
                                                                                            && a2₄₄[i₄₅ := a1₄₂[i₄₅]][x₁₆] == a1₄₂[i₁₅])))
                                                                            && (forall x₁₆: int ::
                                                                                  (!((exists i₁₅: int ::
                                                                                          x₁₆ == i₁₅
                                                                                          && 0 <= i₁₅
                                                                                          && i₁₅ < i₄₅ + 1)
                                                                                  )
                                                                                     ==> a2₄₄[i₄₅ := a1₄₂[i₄₅]][x₁₆] == a2[x₁₆]))
                                                                            && (forall i₁₅: int ::
                                                                                  (  i₁₅ <= i₁₅
                                                                                    && 0 <= i₁₅
                                                                                    && i₁₅ < i₄₅ + 1
                                                                                     ==> i₁₅ < 100000))
                                                                            && true
                                                                            && (true
                                                                               ==> true))
                                                                        && (!(i₄₅ < 100000
                                                                        )
                                                                           ==> true
                                                                            && (true
                                                                               ==> true
                                                                                && 0 <= 0
                                                                                && 0 <= 100000
                                                                                && (forall x₂₀: int ::
                                                                                      ((exists i₁₉: int ::
                                                                                              x₂₀ == i₁₉
                                                                                              && 0 <= i₁₉
                                                                                              && i₁₉ < 0)
                                                                                         ==> (exists i₁₉: int ::
                                                                                                i₁₉ < 100000
                                                                                                && x₂₀ == i₁₉
                                                                                                && 0 <= i₁₉
                                                                                                && i₁₉ < 0
                                                                                                && a3[x₂₀] == a2₄₄[i₁₉])))
                                                                                && (forall x₂₀: int ::
                                                                                      (!((exists i₁₉: int ::
                                                                                              x₂₀ == i₁₉
                                                                                              && 0 <= i₁₉
                                                                                              && i₁₉ < 0)
                                                                                      )
                                                                                         ==> a3[x₂₀] == a3[x₂₀]))
                                                                                && (forall i₁₉: int ::
                                                                                      (  i₁₉ <= i₁₉
                                                                                        && 0 <= i₁₉
                                                                                        && i₁₉ < 0
                                                                                         ==> i₁₉ < 100000))
                                                                                && (forall a3₄₆: [int]int, i₄₇: int ::
                                                                                      (  true
                                                                                        && 0 <= i₄₇
                                                                                        && i₄₇ <= 100000
                                                                                        && (forall x₂₀: int ::
                                                                                              ((exists i₁₉: int ::
                                                                                                      x₂₀ == i₁₉
                                                                                                      && 0 <= i₁₉
                                                                                                      && i₁₉ < i₄₇)
                                                                                                 ==> (exists i₁₉: int ::
                                                                                                        i₁₉ < 100000
                                                                                                        && x₂₀ == i₁₉
                                                                                                        && 0 <= i₁₉
                                                                                                        && i₁₉ < i₄₇
                                                                                                        && a3₄₆[x₂₀] == a2₄₄[i₁₉])))
                                                                                        && (forall x₂₀: int ::
                                                                                              (!((exists i₁₉: int ::
                                                                                                      x₂₀ == i₁₉
                                                                                                      && 0 <= i₁₉
                                                                                                      && i₁₉ < i₄₇)
                                                                                              )
                                                                                                 ==> a3₄₆[x₂₀] == a3[x₂₀]))
                                                                                        && (forall i₁₉: int ::
                                                                                              (  i₁₉ <= i₁₉
                                                                                                && 0 <= i₁₉
                                                                                                && i₁₉ < i₄₇
                                                                                                 ==> i₁₉ < 100000))
                                                                                         ==> (i₄₇ < 100000
                                                                                             ==> true
                                                                                              && 0 <= i₄₇ + 1
                                                                                              && i₄₇ + 1 <= 100000
                                                                                              && (forall x₂₀: int ::
                                                                                                    ((exists i₁₉: int ::
                                                                                                            x₂₀ == i₁₉
                                                                                                            && 0 <= i₁₉
                                                                                                            && i₁₉ < i₄₇ + 1)
                                                                                                       ==> (exists i₁₉: int ::
                                                                                                              i₁₉ < 100000
                                                                                                              && x₂₀ == i₁₉
                                                                                                              && 0 <= i₁₉
                                                                                                              && i₁₉ < i₄₇ + 1
                                                                                                              && a3₄₆[i₄₇ := a2₄₄[i₄₇]][x₂₀] == a2₄₄[i₁₉])))
                                                                                              && (forall x₂₀: int ::
                                                                                                    (!((exists i₁₉: int ::
                                                                                                            x₂₀ == i₁₉
                                                                                                            && 0 <= i₁₉
                                                                                                            && i₁₉ < i₄₇ + 1)
                                                                                                    )
                                                                                                       ==> a3₄₆[i₄₇ := a2₄₄[i₄₇]][x₂₀] == a3[x₂₀]))
                                                                                              && (forall i₁₉: int ::
                                                                                                    (  i₁₉ <= i₁₉
                                                                                                      && 0 <= i₁₉
                                                                                                      && i₁₉ < i₄₇ + 1
                                                                                                       ==> i₁₉ < 100000))
                                                                                              && true
                                                                                              && (true
                                                                                                 ==> true))
                                                                                          && (!(i₄₇ < 100000
                                                                                          )
                                                                                             ==> true
                                                                                              && (true
                                                                                                 ==> true
                                                                                                  && 0 <= 0
                                                                                                  && 0 <= 100000
                                                                                                  && (forall x₂₄: int ::
                                                                                                        ((exists i₂₃: int ::
                                                                                                                x₂₄ == i₂₃
                                                                                                                && 0 <= i₂₃
                                                                                                                && i₂₃ < 0)
                                                                                                           ==> (exists i₂₃: int ::
                                                                                                                  i₂₃ < 100000
                                                                                                                  && x₂₄ == i₂₃
                                                                                                                  && 0 <= i₂₃
                                                                                                                  && i₂₃ < 0
                                                                                                                  && a4[x₂₄] == a3₄₆[i₂₃])))
                                                                                                  && (forall x₂₄: int ::
                                                                                                        (!((exists i₂₃: int ::
                                                                                                                x₂₄ == i₂₃
                                                                                                                && 0 <= i₂₃
                                                                                                                && i₂₃ < 0)
                                                                                                        )
                                                                                                           ==> a4[x₂₄] == a4[x₂₄]))
                                                                                                  && (forall i₂₃: int ::
                                                                                                        (  i₂₃ <= i₂₃
                                                                                                          && 0 <= i₂₃
                                                                                                          && i₂₃ < 0
                                                                                                           ==> i₂₃ < 100000))
                                                                                                  && (forall a4₄₈: [int]int, i₄₉: int ::
                                                                                                        (  true
                                                                                                          && 0 <= i₄₉
                                                                                                          && i₄₉ <= 100000
                                                                                                          && (forall x₂₄: int ::
                                                                                                                ((exists i₂₃: int ::
                                                                                                                        x₂₄ == i₂₃
                                                                                                                        && 0 <= i₂₃
                                                                                                                        && i₂₃ < i₄₉)
                                                                                                                   ==> (exists i₂₃: int ::
                                                                                                                          i₂₃ < 100000
                                                                                                                          && x₂₄ == i₂₃
                                                                                                                          && 0 <= i₂₃
                                                                                                                          && i₂₃ < i₄₉
                                                                                                                          && a4₄₈[x₂₄] == a3₄₆[i₂₃])))
                                                                                                          && (forall x₂₄: int ::
                                                                                                                (!((exists i₂₃: int ::
                                                                                                                        x₂₄ == i₂₃
                                                                                                                        && 0 <= i₂₃
                                                                                                                        && i₂₃ < i₄₉)
                                                                                                                )
                                                                                                                   ==> a4₄₈[x₂₄] == a4[x₂₄]))
                                                                                                          && (forall i₂₃: int ::
                                                                                                                (  i₂₃ <= i₂₃
                                                                                                                  && 0 <= i₂₃
                                                                                                                  && i₂₃ < i₄₉
                                                                                                                   ==> i₂₃ < 100000))
                                                                                                           ==> (i₄₉ < 100000
                                                                                                               ==> true
                                                                                                                && 0 <= i₄₉ + 1
                                                                                                                && i₄₉ + 1 <= 100000
                                                                                                                && (forall x₂₄: int ::
                                                                                                                      ((exists i₂₃: int ::
                                                                                                                              x₂₄ == i₂₃
                                                                                                                              && 0 <= i₂₃
                                                                                                                              && i₂₃ < i₄₉ + 1)
                                                                                                                         ==> (exists i₂₃: int ::
                                                                                                                                i₂₃ < 100000
                                                                                                                                && x₂₄ == i₂₃
                                                                                                                                && 0 <= i₂₃
                                                                                                                                && i₂₃ < i₄₉ + 1
                                                                                                                                && a4₄₈[i₄₉ := a3₄₆[i₄₉]][x₂₄] == a3₄₆[i₂₃])))
                                                                                                                && (forall x₂₄: int ::
                                                                                                                      (!((exists i₂₃: int ::
                                                                                                                              x₂₄ == i₂₃
                                                                                                                              && 0 <= i₂₃
                                                                                                                              && i₂₃ < i₄₉ + 1)
                                                                                                                      )
                                                                                                                         ==> a4₄₈[i₄₉ := a3₄₆[i₄₉]][x₂₄] == a4[x₂₄]))
                                                                                                                && (forall i₂₃: int ::
                                                                                                                      (  i₂₃ <= i₂₃
                                                                                                                        && 0 <= i₂₃
                                                                                                                        && i₂₃ < i₄₉ + 1
                                                                                                                         ==> i₂₃ < 100000))
                                                                                                                && true
                                                                                                                && (true
                                                                                                                   ==> true))
                                                                                                            && (!(i₄₉ < 100000
                                                                                                            )
                                                                                                               ==> true
                                                                                                                && (true
                                                                                                                   ==> true
                                                                                                                    && 0 <= 0
                                                                                                                    && 0 <= 100000
                                                                                                                    && (forall x₂₈: int ::
                                                                                                                          ((exists i₂₇: int ::
                                                                                                                                  x₂₈ == i₂₇
                                                                                                                                  && 0 <= i₂₇
                                                                                                                                  && i₂₇ < 0)
                                                                                                                             ==> (exists i₂₇: int ::
                                                                                                                                    i₂₇ < 100000
                                                                                                                                    && x₂₈ == i₂₇
                                                                                                                                    && 0 <= i₂₇
                                                                                                                                    && i₂₇ < 0
                                                                                                                                    && a5[x₂₈] == a4₄₈[i₂₇])))
                                                                                                                    && (forall x₂₈: int ::
                                                                                                                          (!((exists i₂₇: int ::
                                                                                                                                  x₂₈ == i₂₇
                                                                                                                                  && 0 <= i₂₇
                                                                                                                                  && i₂₇ < 0)
                                                                                                                          )
                                                                                                                             ==> a5[x₂₈] == a5[x₂₈]))
                                                                                                                    && (forall i₂₇: int ::
                                                                                                                          (  i₂₇ <= i₂₇
                                                                                                                            && 0 <= i₂₇
                                                                                                                            && i₂₇ < 0
                                                                                                                             ==> i₂₇ < 100000))
                                                                                                                    && (forall a5₅₀: [int]int, i₅₁: int ::
                                                                                                                          (  true
                                                                                                                            && 0 <= i₅₁
                                                                                                                            && i₅₁ <= 100000
                                                                                                                            && (forall x₂₈: int ::
                                                                                                                                  ((exists i₂₇: int ::
                                                                                                                                          x₂₈ == i₂₇
                                                                                                                                          && 0 <= i₂₇
                                                                                                                                          && i₂₇ < i₅₁)
                                                                                                                                     ==> (exists i₂₇: int ::
                                                                                                                                            i₂₇ < 100000
                                                                                                                                            && x₂₈ == i₂₇
                                                                                                                                            && 0 <= i₂₇
                                                                                                                                            && i₂₇ < i₅₁
                                                                                                                                            && a5₅₀[x₂₈] == a4₄₈[i₂₇])))
                                                                                                                            && (forall x₂₈: int ::
                                                                                                                                  (!((exists i₂₇: int ::
                                                                                                                                          x₂₈ == i₂₇
                                                                                                                                          && 0 <= i₂₇
                                                                                                                                          && i₂₇ < i₅₁)
                                                                                                                                  )
                                                                                                                                     ==> a5₅₀[x₂₈] == a5[x₂₈]))
                                                                                                                            && (forall i₂₇: int ::
                                                                                                                                  (  i₂₇ <= i₂₇
                                                                                                                                    && 0 <= i₂₇
                                                                                                                                    && i₂₇ < i₅₁
                                                                                                                                     ==> i₂₇ < 100000))
                                                                                                                             ==> (i₅₁ < 100000
                                                                                                                                 ==> true
                                                                                                                                  && 0 <= i₅₁ + 1
                                                                                                                                  && i₅₁ + 1 <= 100000
                                                                                                                                  && (forall x₂₈: int ::
                                                                                                                                        ((exists i₂₇: int ::
                                                                                                                                                x₂₈ == i₂₇
                                                                                                                                                && 0 <= i₂₇
                                                                                                                                                && i₂₇ < i₅₁ + 1)
                                                                                                                                           ==> (exists i₂₇: int ::
                                                                                                                                                  i₂₇ < 100000
                                                                                                                                                  && x₂₈ == i₂₇
                                                                                                                                                  && 0 <= i₂₇
                                                                                                                                                  && i₂₇ < i₅₁ + 1
                                                                                                                                                  && a5₅₀[i₅₁ := a4₄₈[i₅₁]][x₂₈] == a4₄₈[i₂₇])))
                                                                                                                                  && (forall x₂₈: int ::
                                                                                                                                        (!((exists i₂₇: int ::
                                                                                                                                                x₂₈ == i₂₇
                                                                                                                                                && 0 <= i₂₇
                                                                                                                                                && i₂₇ < i₅₁ + 1)
                                                                                                                                        )
                                                                                                                                           ==> a5₅₀[i₅₁ := a4₄₈[i₅₁]][x₂₈] == a5[x₂₈]))
                                                                                                                                  && (forall i₂₇: int ::
                                                                                                                                        (  i₂₇ <= i₂₇
                                                                                                                                          && 0 <= i₂₇
                                                                                                                                          && i₂₇ < i₅₁ + 1
                                                                                                                                           ==> i₂₇ < 100000))
                                                                                                                                  && true
                                                                                                                                  && (true
                                                                                                                                     ==> true))
                                                                                                                              && (!(i₅₁ < 100000
                                                                                                                              )
                                                                                                                                 ==> true
                                                                                                                                  && (true
                                                                                                                                     ==> true
                                                                                                                                      && 0 <= 0
                                                                                                                                      && 0 <= 100000
                                                                                                                                      && (forall x₃₂: int ::
                                                                                                                                            ((exists i₃₁: int ::
                                                                                                                                                    x₃₂ == i₃₁
                                                                                                                                                    && 0 <= i₃₁
                                                                                                                                                    && i₃₁ < 0)
                                                                                                                                               ==> (exists i₃₁: int ::
                                                                                                                                                      i₃₁ < 100000
                                                                                                                                                      && x₃₂ == i₃₁
                                                                                                                                                      && 0 <= i₃₁
                                                                                                                                                      && i₃₁ < 0
                                                                                                                                                      && a6[x₃₂] == a5₅₀[i₃₁])))
                                                                                                                                      && (forall x₃₂: int ::
                                                                                                                                            (!((exists i₃₁: int ::
                                                                                                                                                    x₃₂ == i₃₁
                                                                                                                                                    && 0 <= i₃₁
                                                                                                                                                    && i₃₁ < 0)
                                                                                                                                            )
                                                                                                                                               ==> a6[x₃₂] == a6[x₃₂]))
                                                                                                                                      && (forall i₃₁: int ::
                                                                                                                                            (  i₃₁ <= i₃₁
                                                                                                                                              && 0 <= i₃₁
                                                                                                                                              && i₃₁ < 0
                                                                                                                                               ==> i₃₁ < 100000))
                                                                                                                                      && (forall a6₅₂: [int]int, i₅₃: int ::
                                                                                                                                            (  true
                                                                                                                                              && 0 <= i₅₃
                                                                                                                                              && i₅₃ <= 100000
                                                                                                                                              && (forall x₃₂: int ::
                                                                                                                                                    ((exists i₃₁: int ::
                                                                                                                                                            x₃₂ == i₃₁
                                                                                                                                                            && 0 <= i₃₁
                                                                                                                                                            && i₃₁ < i₅₃)
                                                                                                                                                       ==> (exists i₃₁: int ::
                                                                                                                                                              i₃₁ < 100000
                                                                                                                                                              && x₃₂ == i₃₁
                                                                                                                                                              && 0 <= i₃₁
                                                                                                                                                              && i₃₁ < i₅₃
                                                                                                                                                              && a6₅₂[x₃₂] == a5₅₀[i₃₁])))
                                                                                                                                              && (forall x₃₂: int ::
                                                                                                                                                    (!((exists i₃₁: int ::
                                                                                                                                                            x₃₂ == i₃₁
                                                                                                                                                            && 0 <= i₃₁
                                                                                                                                                            && i₃₁ < i₅₃)
                                                                                                                                                    )
                                                                                                                                                       ==> a6₅₂[x₃₂] == a6[x₃₂]))
                                                                                                                                              && (forall i₃₁: int ::
                                                                                                                                                    (  i₃₁ <= i₃₁
                                                                                                                                                      && 0 <= i₃₁
                                                                                                                                                      && i₃₁ < i₅₃
                                                                                                                                                       ==> i₃₁ < 100000))
                                                                                                                                               ==> (i₅₃ < 100000
                                                                                                                                                   ==> true
                                                                                                                                                    && 0 <= i₅₃ + 1
                                                                                                                                                    && i₅₃ + 1 <= 100000
                                                                                                                                                    && (forall x₃₂: int ::
                                                                                                                                                          ((exists i₃₁: int ::
                                                                                                                                                                  x₃₂ == i₃₁
                                                                                                                                                                  && 0 <= i₃₁
                                                                                                                                                                  && i₃₁ < i₅₃ + 1)
                                                                                                                                                             ==> (exists i₃₁: int ::
                                                                                                                                                                    i₃₁ < 100000
                                                                                                                                                                    && x₃₂ == i₃₁
                                                                                                                                                                    && 0 <= i₃₁
                                                                                                                                                                    && i₃₁ < i₅₃ + 1
                                                                                                                                                                    && a6₅₂[i₅₃ := a5₅₀[i₅₃]][x₃₂] == a5₅₀[i₃₁])))
                                                                                                                                                    && (forall x₃₂: int ::
                                                                                                                                                          (!((exists i₃₁: int ::
                                                                                                                                                                  x₃₂ == i₃₁
                                                                                                                                                                  && 0 <= i₃₁
                                                                                                                                                                  && i₃₁ < i₅₃ + 1)
                                                                                                                                                          )
                                                                                                                                                             ==> a6₅₂[i₅₃ := a5₅₀[i₅₃]][x₃₂] == a6[x₃₂]))
                                                                                                                                                    && (forall i₃₁: int ::
                                                                                                                                                          (  i₃₁ <= i₃₁
                                                                                                                                                            && 0 <= i₃₁
                                                                                                                                                            && i₃₁ < i₅₃ + 1
                                                                                                                                                             ==> i₃₁ < 100000))
                                                                                                                                                    && true
                                                                                                                                                    && (true
                                                                                                                                                       ==> true))
                                                                                                                                                && (!(i₅₃ < 100000
                                                                                                                                                )
                                                                                                                                                   ==> true
                                                                                                                                                    && (true
                                                                                                                                                       ==> true
                                                                                                                                                        && 0 <= 0
                                                                                                                                                        && 0 <= 100000
                                                                                                                                                        && (forall x₃₆: int ::
                                                                                                                                                              ((exists i₃₅: int ::
                                                                                                                                                                      x₃₆ == i₃₅
                                                                                                                                                                      && 0 <= i₃₅
                                                                                                                                                                      && i₃₅ < 0)
                                                                                                                                                                 ==> (exists i₃₅: int ::
                                                                                                                                                                        i₃₅ < 100000
                                                                                                                                                                        && x₃₆ == i₃₅
                                                                                                                                                                        && 0 <= i₃₅
                                                                                                                                                                        && i₃₅ < 0
                                                                                                                                                                        && a7[x₃₆] == a6₅₂[i₃₅])))
                                                                                                                                                        && (forall x₃₆: int ::
                                                                                                                                                              (!((exists i₃₅: int ::
                                                                                                                                                                      x₃₆ == i₃₅
                                                                                                                                                                      && 0 <= i₃₅
                                                                                                                                                                      && i₃₅ < 0)
                                                                                                                                                              )
                                                                                                                                                                 ==> a7[x₃₆] == a7[x₃₆]))
                                                                                                                                                        && (forall i₃₅: int ::
                                                                                                                                                              (  i₃₅ <= i₃₅
                                                                                                                                                                && 0 <= i₃₅
                                                                                                                                                                && i₃₅ < 0
                                                                                                                                                                 ==> i₃₅ < 100000))
                                                                                                                                                        && (forall a7₅₄: [int]int, i₅₅: int ::
                                                                                                                                                              (  true
                                                                                                                                                                && 0 <= i₅₅
                                                                                                                                                                && i₅₅ <= 100000
                                                                                                                                                                && (forall x₃₆: int ::
                                                                                                                                                                      ((exists i₃₅: int ::
                                                                                                                                                                              x₃₆ == i₃₅
                                                                                                                                                                              && 0 <= i₃₅
                                                                                                                                                                              && i₃₅ < i₅₅)
                                                                                                                                                                         ==> (exists i₃₅: int ::
                                                                                                                                                                                i₃₅ < 100000
                                                                                                                                                                                && x₃₆ == i₃₅
                                                                                                                                                                                && 0 <= i₃₅
                                                                                                                                                                                && i₃₅ < i₅₅
                                                                                                                                                                                && a7₅₄[x₃₆] == a6₅₂[i₃₅])))
                                                                                                                                                                && (forall x₃₆: int ::
                                                                                                                                                                      (!((exists i₃₅: int ::
                                                                                                                                                                              x₃₆ == i₃₅
                                                                                                                                                                              && 0 <= i₃₅
                                                                                                                                                                              && i₃₅ < i₅₅)
                                                                                                                                                                      )
                                                                                                                                                                         ==> a7₅₄[x₃₆] == a7[x₃₆]))
                                                                                                                                                                && (forall i₃₅: int ::
                                                                                                                                                                      (  i₃₅ <= i₃₅
                                                                                                                                                                        && 0 <= i₃₅
                                                                                                                                                                        && i₃₅ < i₅₅
                                                                                                                                                                         ==> i₃₅ < 100000))
                                                                                                                                                                 ==> (i₅₅ < 100000
                                                                                                                                                                     ==> true
                                                                                                                                                                      && 0 <= i₅₅ + 1
                                                                                                                                                                      && i₅₅ + 1 <= 100000
                                                                                                                                                                      && (forall x₃₆: int ::
                                                                                                                                                                            ((exists i₃₅: int ::
                                                                                                                                                                                    x₃₆ == i₃₅
                                                                                                                                                                                    && 0 <= i₃₅
                                                                                                                                                                                    && i₃₅ < i₅₅ + 1)
                                                                                                                                                                               ==> (exists i₃₅: int ::
                                                                                                                                                                                      i₃₅ < 100000
                                                                                                                                                                                      && x₃₆ == i₃₅
                                                                                                                                                                                      && 0 <= i₃₅
                                                                                                                                                                                      && i₃₅ < i₅₅ + 1
                                                                                                                                                                                      && a7₅₄[i₅₅ := a6₅₂[i₅₅]][x₃₆] == a6₅₂[i₃₅])))
                                                                                                                                                                      && (forall x₃₆: int ::
                                                                                                                                                                            (!((exists i₃₅: int ::
                                                                                                                                                                                    x₃₆ == i₃₅
                                                                                                                                                                                    && 0 <= i₃₅
                                                                                                                                                                                    && i₃₅ < i₅₅ + 1)
                                                                                                                                                                            )
                                                                                                                                                                               ==> a7₅₄[i₅₅ := a6₅₂[i₅₅]][x₃₆] == a7[x₃₆]))
                                                                                                                                                                      && (forall i₃₅: int ::
                                                                                                                                                                            (  i₃₅ <= i₃₅
                                                                                                                                                                              && 0 <= i₃₅
                                                                                                                                                                              && i₃₅ < i₅₅ + 1
                                                                                                                                                                               ==> i₃₅ < 100000))
                                                                                                                                                                      && true
                                                                                                                                                                      && (true
                                                                                                                                                                         ==> true))
                                                                                                                                                                  && (!(i₅₅ < 100000
                                                                                                                                                                  )
                                                                                                                                                                     ==> true
                                                                                                                                                                      && (true
                                                                                                                                                                         ==> true
                                                                                                                                                                          && 0 <= 0
                                                                                                                                                                          && 0 <= 100000
                                                                                                                                                                          && (forall x₄₀: int ::
                                                                                                                                                                                (  x₄₀ <= x₄₀
                                                                                                                                                                                  && 0 <= x₄₀
                                                                                                                                                                                  && x₄₀ < 0
                                                                                                                                                                                   ==> x₄₀ < 100000))
                                                                                                                                                                          && (forall x₅₆: int ::
                                                                                                                                                                                (  true
                                                                                                                                                                                  && 0 <= x₅₆
                                                                                                                                                                                  && x₅₆ <= 100000
                                                                                                                                                                                  && (forall x₄₀: int ::
                                                                                                                                                                                        (  x₄₀ <= x₄₀
                                                                                                                                                                                          && 0 <= x₄₀
                                                                                                                                                                                          && x₄₀ < x₅₆
                                                                                                                                                                                           ==> x₄₀ < 100000))
                                                                                                                                                                                   ==> (x₅₆ < 100000
                                                                                                                                                                                       ==> a1₄₂[x₅₆] == a7₅₄[x₅₆]
                                                                                                                                                                                        && (true
                                                                                                                                                                                           ==> true
                                                                                                                                                                                            && 0 <= x₅₆ + 1
                                                                                                                                                                                            && x₅₆ + 1 <= 100000
                                                                                                                                                                                            && (forall x₄₀: int ::
                                                                                                                                                                                                  (  x₄₀ <= x₄₀
                                                                                                                                                                                                    && 0 <= x₄₀
                                                                                                                                                                                                    && x₄₀ < x₅₆ + 1
                                                                                                                                                                                                     ==> x₄₀ < 100000))
                                                                                                                                                                                            && true
                                                                                                                                                                                            && (true
                                                                                                                                                                                               ==> true)))
                                                                                                                                                                                    && (!(x₅₆ < 100000
                                                                                                                                                                                    )
                                                                                                                                                                                       ==> true
                                                                                                                                                                                        && (true
                                                                                                                                                                                           ==> true)))))))))))))))))))))))))))))))))))))));


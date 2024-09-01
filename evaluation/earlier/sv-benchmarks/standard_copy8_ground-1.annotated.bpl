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
                                          (forall a8: [int]int ::
                                                (forall a9: [int]int ::
                                                        true
                                                        && 0 <= 0
                                                        && 0 <= 100000
                                                        && (forall x₁₃: int ::
                                                              ((exists a₁₂: int ::
                                                                      x₁₃ == a₁₂
                                                                      && 0 <= a₁₂
                                                                      && a₁₂ < 0)
                                                                 ==> (exists __VERIFIER_nondet_int₁₁₁: int, a₁₂: int ::
                                                                        a₁₂ < 100000
                                                                        && x₁₃ == a₁₂
                                                                        && 0 <= a₁₂
                                                                        && a₁₂ < 0
                                                                        && a1[x₁₃] == __VERIFIER_nondet_int₁₁₁)))
                                                        && (forall x₁₃: int ::
                                                              (!((exists a₁₂: int ::
                                                                      x₁₃ == a₁₂
                                                                      && 0 <= a₁₂
                                                                      && a₁₂ < 0)
                                                              )
                                                                 ==> a1[x₁₃] == a1[x₁₃]))
                                                        && (forall a₁₂: int ::
                                                              (  a₁₂ <= a₁₂
                                                                && 0 <= a₁₂
                                                                && a₁₂ < 0
                                                                 ==> a₁₂ < 100000))
                                                        && (forall a1₅₂: [int]int, a₅₃: int ::
                                                              (  true
                                                                && 0 <= a₅₃
                                                                && a₅₃ <= 100000
                                                                && (forall x₁₃: int ::
                                                                      ((exists a₁₂: int ::
                                                                              x₁₃ == a₁₂
                                                                              && 0 <= a₁₂
                                                                              && a₁₂ < a₅₃)
                                                                         ==> (exists __VERIFIER_nondet_int₁₁₁: int, a₁₂: int ::
                                                                                a₁₂ < 100000
                                                                                && x₁₃ == a₁₂
                                                                                && 0 <= a₁₂
                                                                                && a₁₂ < a₅₃
                                                                                && a1₅₂[x₁₃] == __VERIFIER_nondet_int₁₁₁)))
                                                                && (forall x₁₃: int ::
                                                                      (!((exists a₁₂: int ::
                                                                              x₁₃ == a₁₂
                                                                              && 0 <= a₁₂
                                                                              && a₁₂ < a₅₃)
                                                                      )
                                                                         ==> a1₅₂[x₁₃] == a1[x₁₃]))
                                                                && (forall a₁₂: int ::
                                                                      (  a₁₂ <= a₁₂
                                                                        && 0 <= a₁₂
                                                                        && a₁₂ < a₅₃
                                                                         ==> a₁₂ < 100000))
                                                                 ==> (a₅₃ < 100000
                                                                     ==> (forall __VERIFIER_nondet_int₁: int ::
                                                                            true
                                                                            && 0 <= a₅₃ + 1
                                                                            && a₅₃ + 1 <= 100000
                                                                            && (forall x₁₃: int ::
                                                                                  ((exists a₁₂: int ::
                                                                                          x₁₃ == a₁₂
                                                                                          && 0 <= a₁₂
                                                                                          && a₁₂ < a₅₃ + 1)
                                                                                     ==> (exists __VERIFIER_nondet_int₁₁₁: int, a₁₂: int ::
                                                                                            a₁₂ < 100000
                                                                                            && x₁₃ == a₁₂
                                                                                            && 0 <= a₁₂
                                                                                            && a₁₂ < a₅₃ + 1
                                                                                            && a1₅₂[a₅₃ := __VERIFIER_nondet_int₁][x₁₃] == __VERIFIER_nondet_int₁₁₁)))
                                                                            && (forall x₁₃: int ::
                                                                                  (!((exists a₁₂: int ::
                                                                                          x₁₃ == a₁₂
                                                                                          && 0 <= a₁₂
                                                                                          && a₁₂ < a₅₃ + 1)
                                                                                  )
                                                                                     ==> a1₅₂[a₅₃ := __VERIFIER_nondet_int₁][x₁₃] == a1[x₁₃]))
                                                                            && (forall a₁₂: int ::
                                                                                  (  a₁₂ <= a₁₂
                                                                                    && 0 <= a₁₂
                                                                                    && a₁₂ < a₅₃ + 1
                                                                                     ==> a₁₂ < 100000))
                                                                            && true
                                                                            && (true
                                                                               ==> true)))
                                                                  && (!(a₅₃ < 100000
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
                                                                                          && a2[x₁₈] == a1₅₂[i₁₇])))
                                                                          && (forall x₁₈: int ::
                                                                                (!((exists i₁₇: int ::
                                                                                        x₁₈ == i₁₇
                                                                                        && 0 <= i₁₇
                                                                                        && i₁₇ < 0)
                                                                                )
                                                                                   ==> a2[x₁₈] == a2[x₁₈]))
                                                                          && (forall i₁₇: int ::
                                                                                (  i₁₇ <= i₁₇
                                                                                  && 0 <= i₁₇
                                                                                  && i₁₇ < 0
                                                                                   ==> i₁₇ < 100000))
                                                                          && (forall a2₅₄: [int]int, i₅₅: int ::
                                                                                (  true
                                                                                  && 0 <= i₅₅
                                                                                  && i₅₅ <= 100000
                                                                                  && (forall x₁₈: int ::
                                                                                        ((exists i₁₇: int ::
                                                                                                x₁₈ == i₁₇
                                                                                                && 0 <= i₁₇
                                                                                                && i₁₇ < i₅₅)
                                                                                           ==> (exists i₁₇: int ::
                                                                                                  i₁₇ < 100000
                                                                                                  && x₁₈ == i₁₇
                                                                                                  && 0 <= i₁₇
                                                                                                  && i₁₇ < i₅₅
                                                                                                  && a2₅₄[x₁₈] == a1₅₂[i₁₇])))
                                                                                  && (forall x₁₈: int ::
                                                                                        (!((exists i₁₇: int ::
                                                                                                x₁₈ == i₁₇
                                                                                                && 0 <= i₁₇
                                                                                                && i₁₇ < i₅₅)
                                                                                        )
                                                                                           ==> a2₅₄[x₁₈] == a2[x₁₈]))
                                                                                  && (forall i₁₇: int ::
                                                                                        (  i₁₇ <= i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₅₅
                                                                                           ==> i₁₇ < 100000))
                                                                                   ==> (i₅₅ < 100000
                                                                                       ==> true
                                                                                        && 0 <= i₅₅ + 1
                                                                                        && i₅₅ + 1 <= 100000
                                                                                        && (forall x₁₈: int ::
                                                                                              ((exists i₁₇: int ::
                                                                                                      x₁₈ == i₁₇
                                                                                                      && 0 <= i₁₇
                                                                                                      && i₁₇ < i₅₅ + 1)
                                                                                                 ==> (exists i₁₇: int ::
                                                                                                        i₁₇ < 100000
                                                                                                        && x₁₈ == i₁₇
                                                                                                        && 0 <= i₁₇
                                                                                                        && i₁₇ < i₅₅ + 1
                                                                                                        && a2₅₄[i₅₅ := a1₅₂[i₅₅]][x₁₈] == a1₅₂[i₁₇])))
                                                                                        && (forall x₁₈: int ::
                                                                                              (!((exists i₁₇: int ::
                                                                                                      x₁₈ == i₁₇
                                                                                                      && 0 <= i₁₇
                                                                                                      && i₁₇ < i₅₅ + 1)
                                                                                              )
                                                                                                 ==> a2₅₄[i₅₅ := a1₅₂[i₅₅]][x₁₈] == a2[x₁₈]))
                                                                                        && (forall i₁₇: int ::
                                                                                              (  i₁₇ <= i₁₇
                                                                                                && 0 <= i₁₇
                                                                                                && i₁₇ < i₅₅ + 1
                                                                                                 ==> i₁₇ < 100000))
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
                                                                                                            && a3[x₂₂] == a2₅₄[i₂₁])))
                                                                                            && (forall x₂₂: int ::
                                                                                                  (!((exists i₂₁: int ::
                                                                                                          x₂₂ == i₂₁
                                                                                                          && 0 <= i₂₁
                                                                                                          && i₂₁ < 0)
                                                                                                  )
                                                                                                     ==> a3[x₂₂] == a3[x₂₂]))
                                                                                            && (forall i₂₁: int ::
                                                                                                  (  i₂₁ <= i₂₁
                                                                                                    && 0 <= i₂₁
                                                                                                    && i₂₁ < 0
                                                                                                     ==> i₂₁ < 100000))
                                                                                            && (forall a3₅₆: [int]int, i₅₇: int ::
                                                                                                  (  true
                                                                                                    && 0 <= i₅₇
                                                                                                    && i₅₇ <= 100000
                                                                                                    && (forall x₂₂: int ::
                                                                                                          ((exists i₂₁: int ::
                                                                                                                  x₂₂ == i₂₁
                                                                                                                  && 0 <= i₂₁
                                                                                                                  && i₂₁ < i₅₇)
                                                                                                             ==> (exists i₂₁: int ::
                                                                                                                    i₂₁ < 100000
                                                                                                                    && x₂₂ == i₂₁
                                                                                                                    && 0 <= i₂₁
                                                                                                                    && i₂₁ < i₅₇
                                                                                                                    && a3₅₆[x₂₂] == a2₅₄[i₂₁])))
                                                                                                    && (forall x₂₂: int ::
                                                                                                          (!((exists i₂₁: int ::
                                                                                                                  x₂₂ == i₂₁
                                                                                                                  && 0 <= i₂₁
                                                                                                                  && i₂₁ < i₅₇)
                                                                                                          )
                                                                                                             ==> a3₅₆[x₂₂] == a3[x₂₂]))
                                                                                                    && (forall i₂₁: int ::
                                                                                                          (  i₂₁ <= i₂₁
                                                                                                            && 0 <= i₂₁
                                                                                                            && i₂₁ < i₅₇
                                                                                                             ==> i₂₁ < 100000))
                                                                                                     ==> (i₅₇ < 100000
                                                                                                         ==> true
                                                                                                          && 0 <= i₅₇ + 1
                                                                                                          && i₅₇ + 1 <= 100000
                                                                                                          && (forall x₂₂: int ::
                                                                                                                ((exists i₂₁: int ::
                                                                                                                        x₂₂ == i₂₁
                                                                                                                        && 0 <= i₂₁
                                                                                                                        && i₂₁ < i₅₇ + 1)
                                                                                                                   ==> (exists i₂₁: int ::
                                                                                                                          i₂₁ < 100000
                                                                                                                          && x₂₂ == i₂₁
                                                                                                                          && 0 <= i₂₁
                                                                                                                          && i₂₁ < i₅₇ + 1
                                                                                                                          && a3₅₆[i₅₇ := a2₅₄[i₅₇]][x₂₂] == a2₅₄[i₂₁])))
                                                                                                          && (forall x₂₂: int ::
                                                                                                                (!((exists i₂₁: int ::
                                                                                                                        x₂₂ == i₂₁
                                                                                                                        && 0 <= i₂₁
                                                                                                                        && i₂₁ < i₅₇ + 1)
                                                                                                                )
                                                                                                                   ==> a3₅₆[i₅₇ := a2₅₄[i₅₇]][x₂₂] == a3[x₂₂]))
                                                                                                          && (forall i₂₁: int ::
                                                                                                                (  i₂₁ <= i₂₁
                                                                                                                  && 0 <= i₂₁
                                                                                                                  && i₂₁ < i₅₇ + 1
                                                                                                                   ==> i₂₁ < 100000))
                                                                                                          && true
                                                                                                          && (true
                                                                                                             ==> true))
                                                                                                      && (!(i₅₇ < 100000
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
                                                                                                                              && a4[x₂₆] == a3₅₆[i₂₅])))
                                                                                                              && (forall x₂₆: int ::
                                                                                                                    (!((exists i₂₅: int ::
                                                                                                                            x₂₆ == i₂₅
                                                                                                                            && 0 <= i₂₅
                                                                                                                            && i₂₅ < 0)
                                                                                                                    )
                                                                                                                       ==> a4[x₂₆] == a4[x₂₆]))
                                                                                                              && (forall i₂₅: int ::
                                                                                                                    (  i₂₅ <= i₂₅
                                                                                                                      && 0 <= i₂₅
                                                                                                                      && i₂₅ < 0
                                                                                                                       ==> i₂₅ < 100000))
                                                                                                              && (forall a4₅₈: [int]int, i₅₉: int ::
                                                                                                                    (  true
                                                                                                                      && 0 <= i₅₉
                                                                                                                      && i₅₉ <= 100000
                                                                                                                      && (forall x₂₆: int ::
                                                                                                                            ((exists i₂₅: int ::
                                                                                                                                    x₂₆ == i₂₅
                                                                                                                                    && 0 <= i₂₅
                                                                                                                                    && i₂₅ < i₅₉)
                                                                                                                               ==> (exists i₂₅: int ::
                                                                                                                                      i₂₅ < 100000
                                                                                                                                      && x₂₆ == i₂₅
                                                                                                                                      && 0 <= i₂₅
                                                                                                                                      && i₂₅ < i₅₉
                                                                                                                                      && a4₅₈[x₂₆] == a3₅₆[i₂₅])))
                                                                                                                      && (forall x₂₆: int ::
                                                                                                                            (!((exists i₂₅: int ::
                                                                                                                                    x₂₆ == i₂₅
                                                                                                                                    && 0 <= i₂₅
                                                                                                                                    && i₂₅ < i₅₉)
                                                                                                                            )
                                                                                                                               ==> a4₅₈[x₂₆] == a4[x₂₆]))
                                                                                                                      && (forall i₂₅: int ::
                                                                                                                            (  i₂₅ <= i₂₅
                                                                                                                              && 0 <= i₂₅
                                                                                                                              && i₂₅ < i₅₉
                                                                                                                               ==> i₂₅ < 100000))
                                                                                                                       ==> (i₅₉ < 100000
                                                                                                                           ==> true
                                                                                                                            && 0 <= i₅₉ + 1
                                                                                                                            && i₅₉ + 1 <= 100000
                                                                                                                            && (forall x₂₆: int ::
                                                                                                                                  ((exists i₂₅: int ::
                                                                                                                                          x₂₆ == i₂₅
                                                                                                                                          && 0 <= i₂₅
                                                                                                                                          && i₂₅ < i₅₉ + 1)
                                                                                                                                     ==> (exists i₂₅: int ::
                                                                                                                                            i₂₅ < 100000
                                                                                                                                            && x₂₆ == i₂₅
                                                                                                                                            && 0 <= i₂₅
                                                                                                                                            && i₂₅ < i₅₉ + 1
                                                                                                                                            && a4₅₈[i₅₉ := a3₅₆[i₅₉]][x₂₆] == a3₅₆[i₂₅])))
                                                                                                                            && (forall x₂₆: int ::
                                                                                                                                  (!((exists i₂₅: int ::
                                                                                                                                          x₂₆ == i₂₅
                                                                                                                                          && 0 <= i₂₅
                                                                                                                                          && i₂₅ < i₅₉ + 1)
                                                                                                                                  )
                                                                                                                                     ==> a4₅₈[i₅₉ := a3₅₆[i₅₉]][x₂₆] == a4[x₂₆]))
                                                                                                                            && (forall i₂₅: int ::
                                                                                                                                  (  i₂₅ <= i₂₅
                                                                                                                                    && 0 <= i₂₅
                                                                                                                                    && i₂₅ < i₅₉ + 1
                                                                                                                                     ==> i₂₅ < 100000))
                                                                                                                            && true
                                                                                                                            && (true
                                                                                                                               ==> true))
                                                                                                                        && (!(i₅₉ < 100000
                                                                                                                        )
                                                                                                                           ==> true
                                                                                                                            && (true
                                                                                                                               ==> true
                                                                                                                                && 0 <= 0
                                                                                                                                && 0 <= 100000
                                                                                                                                && (forall x₃₀: int ::
                                                                                                                                      ((exists i₂₉: int ::
                                                                                                                                              x₃₀ == i₂₉
                                                                                                                                              && 0 <= i₂₉
                                                                                                                                              && i₂₉ < 0)
                                                                                                                                         ==> (exists i₂₉: int ::
                                                                                                                                                i₂₉ < 100000
                                                                                                                                                && x₃₀ == i₂₉
                                                                                                                                                && 0 <= i₂₉
                                                                                                                                                && i₂₉ < 0
                                                                                                                                                && a5[x₃₀] == a4₅₈[i₂₉])))
                                                                                                                                && (forall x₃₀: int ::
                                                                                                                                      (!((exists i₂₉: int ::
                                                                                                                                              x₃₀ == i₂₉
                                                                                                                                              && 0 <= i₂₉
                                                                                                                                              && i₂₉ < 0)
                                                                                                                                      )
                                                                                                                                         ==> a5[x₃₀] == a5[x₃₀]))
                                                                                                                                && (forall i₂₉: int ::
                                                                                                                                      (  i₂₉ <= i₂₉
                                                                                                                                        && 0 <= i₂₉
                                                                                                                                        && i₂₉ < 0
                                                                                                                                         ==> i₂₉ < 100000))
                                                                                                                                && (forall a5₆₀: [int]int, i₆₁: int ::
                                                                                                                                      (  true
                                                                                                                                        && 0 <= i₆₁
                                                                                                                                        && i₆₁ <= 100000
                                                                                                                                        && (forall x₃₀: int ::
                                                                                                                                              ((exists i₂₉: int ::
                                                                                                                                                      x₃₀ == i₂₉
                                                                                                                                                      && 0 <= i₂₉
                                                                                                                                                      && i₂₉ < i₆₁)
                                                                                                                                                 ==> (exists i₂₉: int ::
                                                                                                                                                        i₂₉ < 100000
                                                                                                                                                        && x₃₀ == i₂₉
                                                                                                                                                        && 0 <= i₂₉
                                                                                                                                                        && i₂₉ < i₆₁
                                                                                                                                                        && a5₆₀[x₃₀] == a4₅₈[i₂₉])))
                                                                                                                                        && (forall x₃₀: int ::
                                                                                                                                              (!((exists i₂₉: int ::
                                                                                                                                                      x₃₀ == i₂₉
                                                                                                                                                      && 0 <= i₂₉
                                                                                                                                                      && i₂₉ < i₆₁)
                                                                                                                                              )
                                                                                                                                                 ==> a5₆₀[x₃₀] == a5[x₃₀]))
                                                                                                                                        && (forall i₂₉: int ::
                                                                                                                                              (  i₂₉ <= i₂₉
                                                                                                                                                && 0 <= i₂₉
                                                                                                                                                && i₂₉ < i₆₁
                                                                                                                                                 ==> i₂₉ < 100000))
                                                                                                                                         ==> (i₆₁ < 100000
                                                                                                                                             ==> true
                                                                                                                                              && 0 <= i₆₁ + 1
                                                                                                                                              && i₆₁ + 1 <= 100000
                                                                                                                                              && (forall x₃₀: int ::
                                                                                                                                                    ((exists i₂₉: int ::
                                                                                                                                                            x₃₀ == i₂₉
                                                                                                                                                            && 0 <= i₂₉
                                                                                                                                                            && i₂₉ < i₆₁ + 1)
                                                                                                                                                       ==> (exists i₂₉: int ::
                                                                                                                                                              i₂₉ < 100000
                                                                                                                                                              && x₃₀ == i₂₉
                                                                                                                                                              && 0 <= i₂₉
                                                                                                                                                              && i₂₉ < i₆₁ + 1
                                                                                                                                                              && a5₆₀[i₆₁ := a4₅₈[i₆₁]][x₃₀] == a4₅₈[i₂₉])))
                                                                                                                                              && (forall x₃₀: int ::
                                                                                                                                                    (!((exists i₂₉: int ::
                                                                                                                                                            x₃₀ == i₂₉
                                                                                                                                                            && 0 <= i₂₉
                                                                                                                                                            && i₂₉ < i₆₁ + 1)
                                                                                                                                                    )
                                                                                                                                                       ==> a5₆₀[i₆₁ := a4₅₈[i₆₁]][x₃₀] == a5[x₃₀]))
                                                                                                                                              && (forall i₂₉: int ::
                                                                                                                                                    (  i₂₉ <= i₂₉
                                                                                                                                                      && 0 <= i₂₉
                                                                                                                                                      && i₂₉ < i₆₁ + 1
                                                                                                                                                       ==> i₂₉ < 100000))
                                                                                                                                              && true
                                                                                                                                              && (true
                                                                                                                                                 ==> true))
                                                                                                                                          && (!(i₆₁ < 100000
                                                                                                                                          )
                                                                                                                                             ==> true
                                                                                                                                              && (true
                                                                                                                                                 ==> true
                                                                                                                                                  && 0 <= 0
                                                                                                                                                  && 0 <= 100000
                                                                                                                                                  && (forall x₃₄: int ::
                                                                                                                                                        ((exists i₃₃: int ::
                                                                                                                                                                x₃₄ == i₃₃
                                                                                                                                                                && 0 <= i₃₃
                                                                                                                                                                && i₃₃ < 0)
                                                                                                                                                           ==> (exists i₃₃: int ::
                                                                                                                                                                  i₃₃ < 100000
                                                                                                                                                                  && x₃₄ == i₃₃
                                                                                                                                                                  && 0 <= i₃₃
                                                                                                                                                                  && i₃₃ < 0
                                                                                                                                                                  && a6[x₃₄] == a5₆₀[i₃₃])))
                                                                                                                                                  && (forall x₃₄: int ::
                                                                                                                                                        (!((exists i₃₃: int ::
                                                                                                                                                                x₃₄ == i₃₃
                                                                                                                                                                && 0 <= i₃₃
                                                                                                                                                                && i₃₃ < 0)
                                                                                                                                                        )
                                                                                                                                                           ==> a6[x₃₄] == a6[x₃₄]))
                                                                                                                                                  && (forall i₃₃: int ::
                                                                                                                                                        (  i₃₃ <= i₃₃
                                                                                                                                                          && 0 <= i₃₃
                                                                                                                                                          && i₃₃ < 0
                                                                                                                                                           ==> i₃₃ < 100000))
                                                                                                                                                  && (forall a6₆₂: [int]int, i₆₃: int ::
                                                                                                                                                        (  true
                                                                                                                                                          && 0 <= i₆₃
                                                                                                                                                          && i₆₃ <= 100000
                                                                                                                                                          && (forall x₃₄: int ::
                                                                                                                                                                ((exists i₃₃: int ::
                                                                                                                                                                        x₃₄ == i₃₃
                                                                                                                                                                        && 0 <= i₃₃
                                                                                                                                                                        && i₃₃ < i₆₃)
                                                                                                                                                                   ==> (exists i₃₃: int ::
                                                                                                                                                                          i₃₃ < 100000
                                                                                                                                                                          && x₃₄ == i₃₃
                                                                                                                                                                          && 0 <= i₃₃
                                                                                                                                                                          && i₃₃ < i₆₃
                                                                                                                                                                          && a6₆₂[x₃₄] == a5₆₀[i₃₃])))
                                                                                                                                                          && (forall x₃₄: int ::
                                                                                                                                                                (!((exists i₃₃: int ::
                                                                                                                                                                        x₃₄ == i₃₃
                                                                                                                                                                        && 0 <= i₃₃
                                                                                                                                                                        && i₃₃ < i₆₃)
                                                                                                                                                                )
                                                                                                                                                                   ==> a6₆₂[x₃₄] == a6[x₃₄]))
                                                                                                                                                          && (forall i₃₃: int ::
                                                                                                                                                                (  i₃₃ <= i₃₃
                                                                                                                                                                  && 0 <= i₃₃
                                                                                                                                                                  && i₃₃ < i₆₃
                                                                                                                                                                   ==> i₃₃ < 100000))
                                                                                                                                                           ==> (i₆₃ < 100000
                                                                                                                                                               ==> true
                                                                                                                                                                && 0 <= i₆₃ + 1
                                                                                                                                                                && i₆₃ + 1 <= 100000
                                                                                                                                                                && (forall x₃₄: int ::
                                                                                                                                                                      ((exists i₃₃: int ::
                                                                                                                                                                              x₃₄ == i₃₃
                                                                                                                                                                              && 0 <= i₃₃
                                                                                                                                                                              && i₃₃ < i₆₃ + 1)
                                                                                                                                                                         ==> (exists i₃₃: int ::
                                                                                                                                                                                i₃₃ < 100000
                                                                                                                                                                                && x₃₄ == i₃₃
                                                                                                                                                                                && 0 <= i₃₃
                                                                                                                                                                                && i₃₃ < i₆₃ + 1
                                                                                                                                                                                && a6₆₂[i₆₃ := a5₆₀[i₆₃]][x₃₄] == a5₆₀[i₃₃])))
                                                                                                                                                                && (forall x₃₄: int ::
                                                                                                                                                                      (!((exists i₃₃: int ::
                                                                                                                                                                              x₃₄ == i₃₃
                                                                                                                                                                              && 0 <= i₃₃
                                                                                                                                                                              && i₃₃ < i₆₃ + 1)
                                                                                                                                                                      )
                                                                                                                                                                         ==> a6₆₂[i₆₃ := a5₆₀[i₆₃]][x₃₄] == a6[x₃₄]))
                                                                                                                                                                && (forall i₃₃: int ::
                                                                                                                                                                      (  i₃₃ <= i₃₃
                                                                                                                                                                        && 0 <= i₃₃
                                                                                                                                                                        && i₃₃ < i₆₃ + 1
                                                                                                                                                                         ==> i₃₃ < 100000))
                                                                                                                                                                && true
                                                                                                                                                                && (true
                                                                                                                                                                   ==> true))
                                                                                                                                                            && (!(i₆₃ < 100000
                                                                                                                                                            )
                                                                                                                                                               ==> true
                                                                                                                                                                && (true
                                                                                                                                                                   ==> true
                                                                                                                                                                    && 0 <= 0
                                                                                                                                                                    && 0 <= 100000
                                                                                                                                                                    && (forall x₃₈: int ::
                                                                                                                                                                          ((exists i₃₇: int ::
                                                                                                                                                                                  x₃₈ == i₃₇
                                                                                                                                                                                  && 0 <= i₃₇
                                                                                                                                                                                  && i₃₇ < 0)
                                                                                                                                                                             ==> (exists i₃₇: int ::
                                                                                                                                                                                    i₃₇ < 100000
                                                                                                                                                                                    && x₃₈ == i₃₇
                                                                                                                                                                                    && 0 <= i₃₇
                                                                                                                                                                                    && i₃₇ < 0
                                                                                                                                                                                    && a7[x₃₈] == a6₆₂[i₃₇])))
                                                                                                                                                                    && (forall x₃₈: int ::
                                                                                                                                                                          (!((exists i₃₇: int ::
                                                                                                                                                                                  x₃₈ == i₃₇
                                                                                                                                                                                  && 0 <= i₃₇
                                                                                                                                                                                  && i₃₇ < 0)
                                                                                                                                                                          )
                                                                                                                                                                             ==> a7[x₃₈] == a7[x₃₈]))
                                                                                                                                                                    && (forall i₃₇: int ::
                                                                                                                                                                          (  i₃₇ <= i₃₇
                                                                                                                                                                            && 0 <= i₃₇
                                                                                                                                                                            && i₃₇ < 0
                                                                                                                                                                             ==> i₃₇ < 100000))
                                                                                                                                                                    && (forall a7₆₄: [int]int, i₆₅: int ::
                                                                                                                                                                          (  true
                                                                                                                                                                            && 0 <= i₆₅
                                                                                                                                                                            && i₆₅ <= 100000
                                                                                                                                                                            && (forall x₃₈: int ::
                                                                                                                                                                                  ((exists i₃₇: int ::
                                                                                                                                                                                          x₃₈ == i₃₇
                                                                                                                                                                                          && 0 <= i₃₇
                                                                                                                                                                                          && i₃₇ < i₆₅)
                                                                                                                                                                                     ==> (exists i₃₇: int ::
                                                                                                                                                                                            i₃₇ < 100000
                                                                                                                                                                                            && x₃₈ == i₃₇
                                                                                                                                                                                            && 0 <= i₃₇
                                                                                                                                                                                            && i₃₇ < i₆₅
                                                                                                                                                                                            && a7₆₄[x₃₈] == a6₆₂[i₃₇])))
                                                                                                                                                                            && (forall x₃₈: int ::
                                                                                                                                                                                  (!((exists i₃₇: int ::
                                                                                                                                                                                          x₃₈ == i₃₇
                                                                                                                                                                                          && 0 <= i₃₇
                                                                                                                                                                                          && i₃₇ < i₆₅)
                                                                                                                                                                                  )
                                                                                                                                                                                     ==> a7₆₄[x₃₈] == a7[x₃₈]))
                                                                                                                                                                            && (forall i₃₇: int ::
                                                                                                                                                                                  (  i₃₇ <= i₃₇
                                                                                                                                                                                    && 0 <= i₃₇
                                                                                                                                                                                    && i₃₇ < i₆₅
                                                                                                                                                                                     ==> i₃₇ < 100000))
                                                                                                                                                                             ==> (i₆₅ < 100000
                                                                                                                                                                                 ==> true
                                                                                                                                                                                  && 0 <= i₆₅ + 1
                                                                                                                                                                                  && i₆₅ + 1 <= 100000
                                                                                                                                                                                  && (forall x₃₈: int ::
                                                                                                                                                                                        ((exists i₃₇: int ::
                                                                                                                                                                                                x₃₈ == i₃₇
                                                                                                                                                                                                && 0 <= i₃₇
                                                                                                                                                                                                && i₃₇ < i₆₅ + 1)
                                                                                                                                                                                           ==> (exists i₃₇: int ::
                                                                                                                                                                                                  i₃₇ < 100000
                                                                                                                                                                                                  && x₃₈ == i₃₇
                                                                                                                                                                                                  && 0 <= i₃₇
                                                                                                                                                                                                  && i₃₇ < i₆₅ + 1
                                                                                                                                                                                                  && a7₆₄[i₆₅ := a6₆₂[i₆₅]][x₃₈] == a6₆₂[i₃₇])))
                                                                                                                                                                                  && (forall x₃₈: int ::
                                                                                                                                                                                        (!((exists i₃₇: int ::
                                                                                                                                                                                                x₃₈ == i₃₇
                                                                                                                                                                                                && 0 <= i₃₇
                                                                                                                                                                                                && i₃₇ < i₆₅ + 1)
                                                                                                                                                                                        )
                                                                                                                                                                                           ==> a7₆₄[i₆₅ := a6₆₂[i₆₅]][x₃₈] == a7[x₃₈]))
                                                                                                                                                                                  && (forall i₃₇: int ::
                                                                                                                                                                                        (  i₃₇ <= i₃₇
                                                                                                                                                                                          && 0 <= i₃₇
                                                                                                                                                                                          && i₃₇ < i₆₅ + 1
                                                                                                                                                                                           ==> i₃₇ < 100000))
                                                                                                                                                                                  && true
                                                                                                                                                                                  && (true
                                                                                                                                                                                     ==> true))
                                                                                                                                                                              && (!(i₆₅ < 100000
                                                                                                                                                                              )
                                                                                                                                                                                 ==> true
                                                                                                                                                                                  && (true
                                                                                                                                                                                     ==> true
                                                                                                                                                                                      && 0 <= 0
                                                                                                                                                                                      && 0 <= 100000
                                                                                                                                                                                      && (forall x₄₂: int ::
                                                                                                                                                                                            ((exists i₄₁: int ::
                                                                                                                                                                                                    x₄₂ == i₄₁
                                                                                                                                                                                                    && 0 <= i₄₁
                                                                                                                                                                                                    && i₄₁ < 0)
                                                                                                                                                                                               ==> (exists i₄₁: int ::
                                                                                                                                                                                                      i₄₁ < 100000
                                                                                                                                                                                                      && x₄₂ == i₄₁
                                                                                                                                                                                                      && 0 <= i₄₁
                                                                                                                                                                                                      && i₄₁ < 0
                                                                                                                                                                                                      && a8[x₄₂] == a7₆₄[i₄₁])))
                                                                                                                                                                                      && (forall x₄₂: int ::
                                                                                                                                                                                            (!((exists i₄₁: int ::
                                                                                                                                                                                                    x₄₂ == i₄₁
                                                                                                                                                                                                    && 0 <= i₄₁
                                                                                                                                                                                                    && i₄₁ < 0)
                                                                                                                                                                                            )
                                                                                                                                                                                               ==> a8[x₄₂] == a8[x₄₂]))
                                                                                                                                                                                      && (forall i₄₁: int ::
                                                                                                                                                                                            (  i₄₁ <= i₄₁
                                                                                                                                                                                              && 0 <= i₄₁
                                                                                                                                                                                              && i₄₁ < 0
                                                                                                                                                                                               ==> i₄₁ < 100000))
                                                                                                                                                                                      && (forall a8₆₆: [int]int, i₆₇: int ::
                                                                                                                                                                                            (  true
                                                                                                                                                                                              && 0 <= i₆₇
                                                                                                                                                                                              && i₆₇ <= 100000
                                                                                                                                                                                              && (forall x₄₂: int ::
                                                                                                                                                                                                    ((exists i₄₁: int ::
                                                                                                                                                                                                            x₄₂ == i₄₁
                                                                                                                                                                                                            && 0 <= i₄₁
                                                                                                                                                                                                            && i₄₁ < i₆₇)
                                                                                                                                                                                                       ==> (exists i₄₁: int ::
                                                                                                                                                                                                              i₄₁ < 100000
                                                                                                                                                                                                              && x₄₂ == i₄₁
                                                                                                                                                                                                              && 0 <= i₄₁
                                                                                                                                                                                                              && i₄₁ < i₆₇
                                                                                                                                                                                                              && a8₆₆[x₄₂] == a7₆₄[i₄₁])))
                                                                                                                                                                                              && (forall x₄₂: int ::
                                                                                                                                                                                                    (!((exists i₄₁: int ::
                                                                                                                                                                                                            x₄₂ == i₄₁
                                                                                                                                                                                                            && 0 <= i₄₁
                                                                                                                                                                                                            && i₄₁ < i₆₇)
                                                                                                                                                                                                    )
                                                                                                                                                                                                       ==> a8₆₆[x₄₂] == a8[x₄₂]))
                                                                                                                                                                                              && (forall i₄₁: int ::
                                                                                                                                                                                                    (  i₄₁ <= i₄₁
                                                                                                                                                                                                      && 0 <= i₄₁
                                                                                                                                                                                                      && i₄₁ < i₆₇
                                                                                                                                                                                                       ==> i₄₁ < 100000))
                                                                                                                                                                                               ==> (i₆₇ < 100000
                                                                                                                                                                                                   ==> true
                                                                                                                                                                                                    && 0 <= i₆₇ + 1
                                                                                                                                                                                                    && i₆₇ + 1 <= 100000
                                                                                                                                                                                                    && (forall x₄₂: int ::
                                                                                                                                                                                                          ((exists i₄₁: int ::
                                                                                                                                                                                                                  x₄₂ == i₄₁
                                                                                                                                                                                                                  && 0 <= i₄₁
                                                                                                                                                                                                                  && i₄₁ < i₆₇ + 1)
                                                                                                                                                                                                             ==> (exists i₄₁: int ::
                                                                                                                                                                                                                    i₄₁ < 100000
                                                                                                                                                                                                                    && x₄₂ == i₄₁
                                                                                                                                                                                                                    && 0 <= i₄₁
                                                                                                                                                                                                                    && i₄₁ < i₆₇ + 1
                                                                                                                                                                                                                    && a8₆₆[i₆₇ := a7₆₄[i₆₇]][x₄₂] == a7₆₄[i₄₁])))
                                                                                                                                                                                                    && (forall x₄₂: int ::
                                                                                                                                                                                                          (!((exists i₄₁: int ::
                                                                                                                                                                                                                  x₄₂ == i₄₁
                                                                                                                                                                                                                  && 0 <= i₄₁
                                                                                                                                                                                                                  && i₄₁ < i₆₇ + 1)
                                                                                                                                                                                                          )
                                                                                                                                                                                                             ==> a8₆₆[i₆₇ := a7₆₄[i₆₇]][x₄₂] == a8[x₄₂]))
                                                                                                                                                                                                    && (forall i₄₁: int ::
                                                                                                                                                                                                          (  i₄₁ <= i₄₁
                                                                                                                                                                                                            && 0 <= i₄₁
                                                                                                                                                                                                            && i₄₁ < i₆₇ + 1
                                                                                                                                                                                                             ==> i₄₁ < 100000))
                                                                                                                                                                                                    && true
                                                                                                                                                                                                    && (true
                                                                                                                                                                                                       ==> true))
                                                                                                                                                                                                && (!(i₆₇ < 100000
                                                                                                                                                                                                )
                                                                                                                                                                                                   ==> true
                                                                                                                                                                                                    && (true
                                                                                                                                                                                                       ==> true
                                                                                                                                                                                                        && 0 <= 0
                                                                                                                                                                                                        && 0 <= 100000
                                                                                                                                                                                                        && (forall x₄₆: int ::
                                                                                                                                                                                                              ((exists i₄₅: int ::
                                                                                                                                                                                                                      x₄₆ == i₄₅
                                                                                                                                                                                                                      && 0 <= i₄₅
                                                                                                                                                                                                                      && i₄₅ < 0)
                                                                                                                                                                                                                 ==> (exists i₄₅: int ::
                                                                                                                                                                                                                        i₄₅ < 100000
                                                                                                                                                                                                                        && x₄₆ == i₄₅
                                                                                                                                                                                                                        && 0 <= i₄₅
                                                                                                                                                                                                                        && i₄₅ < 0
                                                                                                                                                                                                                        && a9[x₄₆] == a8₆₆[i₄₅])))
                                                                                                                                                                                                        && (forall x₄₆: int ::
                                                                                                                                                                                                              (!((exists i₄₅: int ::
                                                                                                                                                                                                                      x₄₆ == i₄₅
                                                                                                                                                                                                                      && 0 <= i₄₅
                                                                                                                                                                                                                      && i₄₅ < 0)
                                                                                                                                                                                                              )
                                                                                                                                                                                                                 ==> a9[x₄₆] == a9[x₄₆]))
                                                                                                                                                                                                        && (forall i₄₅: int ::
                                                                                                                                                                                                              (  i₄₅ <= i₄₅
                                                                                                                                                                                                                && 0 <= i₄₅
                                                                                                                                                                                                                && i₄₅ < 0
                                                                                                                                                                                                                 ==> i₄₅ < 100000))
                                                                                                                                                                                                        && (forall a9₆₈: [int]int, i₆₉: int ::
                                                                                                                                                                                                              (  true
                                                                                                                                                                                                                && 0 <= i₆₉
                                                                                                                                                                                                                && i₆₉ <= 100000
                                                                                                                                                                                                                && (forall x₄₆: int ::
                                                                                                                                                                                                                      ((exists i₄₅: int ::
                                                                                                                                                                                                                              x₄₆ == i₄₅
                                                                                                                                                                                                                              && 0 <= i₄₅
                                                                                                                                                                                                                              && i₄₅ < i₆₉)
                                                                                                                                                                                                                         ==> (exists i₄₅: int ::
                                                                                                                                                                                                                                i₄₅ < 100000
                                                                                                                                                                                                                                && x₄₆ == i₄₅
                                                                                                                                                                                                                                && 0 <= i₄₅
                                                                                                                                                                                                                                && i₄₅ < i₆₉
                                                                                                                                                                                                                                && a9₆₈[x₄₆] == a8₆₆[i₄₅])))
                                                                                                                                                                                                                && (forall x₄₆: int ::
                                                                                                                                                                                                                      (!((exists i₄₅: int ::
                                                                                                                                                                                                                              x₄₆ == i₄₅
                                                                                                                                                                                                                              && 0 <= i₄₅
                                                                                                                                                                                                                              && i₄₅ < i₆₉)
                                                                                                                                                                                                                      )
                                                                                                                                                                                                                         ==> a9₆₈[x₄₆] == a9[x₄₆]))
                                                                                                                                                                                                                && (forall i₄₅: int ::
                                                                                                                                                                                                                      (  i₄₅ <= i₄₅
                                                                                                                                                                                                                        && 0 <= i₄₅
                                                                                                                                                                                                                        && i₄₅ < i₆₉
                                                                                                                                                                                                                         ==> i₄₅ < 100000))
                                                                                                                                                                                                                 ==> (i₆₉ < 100000
                                                                                                                                                                                                                     ==> true
                                                                                                                                                                                                                      && 0 <= i₆₉ + 1
                                                                                                                                                                                                                      && i₆₉ + 1 <= 100000
                                                                                                                                                                                                                      && (forall x₄₆: int ::
                                                                                                                                                                                                                            ((exists i₄₅: int ::
                                                                                                                                                                                                                                    x₄₆ == i₄₅
                                                                                                                                                                                                                                    && 0 <= i₄₅
                                                                                                                                                                                                                                    && i₄₅ < i₆₉ + 1)
                                                                                                                                                                                                                               ==> (exists i₄₅: int ::
                                                                                                                                                                                                                                      i₄₅ < 100000
                                                                                                                                                                                                                                      && x₄₆ == i₄₅
                                                                                                                                                                                                                                      && 0 <= i₄₅
                                                                                                                                                                                                                                      && i₄₅ < i₆₉ + 1
                                                                                                                                                                                                                                      && a9₆₈[i₆₉ := a8₆₆[i₆₉]][x₄₆] == a8₆₆[i₄₅])))
                                                                                                                                                                                                                      && (forall x₄₆: int ::
                                                                                                                                                                                                                            (!((exists i₄₅: int ::
                                                                                                                                                                                                                                    x₄₆ == i₄₅
                                                                                                                                                                                                                                    && 0 <= i₄₅
                                                                                                                                                                                                                                    && i₄₅ < i₆₉ + 1)
                                                                                                                                                                                                                            )
                                                                                                                                                                                                                               ==> a9₆₈[i₆₉ := a8₆₆[i₆₉]][x₄₆] == a9[x₄₆]))
                                                                                                                                                                                                                      && (forall i₄₅: int ::
                                                                                                                                                                                                                            (  i₄₅ <= i₄₅
                                                                                                                                                                                                                              && 0 <= i₄₅
                                                                                                                                                                                                                              && i₄₅ < i₆₉ + 1
                                                                                                                                                                                                                               ==> i₄₅ < 100000))
                                                                                                                                                                                                                      && true
                                                                                                                                                                                                                      && (true
                                                                                                                                                                                                                         ==> true))
                                                                                                                                                                                                                  && (!(i₆₉ < 100000
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                     ==> true
                                                                                                                                                                                                                      && (true
                                                                                                                                                                                                                         ==> true
                                                                                                                                                                                                                          && 0 <= 0
                                                                                                                                                                                                                          && 0 <= 100000
                                                                                                                                                                                                                          && (forall x₅₀: int ::
                                                                                                                                                                                                                                (  x₅₀ <= x₅₀
                                                                                                                                                                                                                                  && 0 <= x₅₀
                                                                                                                                                                                                                                  && x₅₀ < 0
                                                                                                                                                                                                                                   ==> x₅₀ < 100000))
                                                                                                                                                                                                                          && (forall x₇₀: int ::
                                                                                                                                                                                                                                (  true
                                                                                                                                                                                                                                  && 0 <= x₇₀
                                                                                                                                                                                                                                  && x₇₀ <= 100000
                                                                                                                                                                                                                                  && (forall x₅₀: int ::
                                                                                                                                                                                                                                        (  x₅₀ <= x₅₀
                                                                                                                                                                                                                                          && 0 <= x₅₀
                                                                                                                                                                                                                                          && x₅₀ < x₇₀
                                                                                                                                                                                                                                           ==> x₅₀ < 100000))
                                                                                                                                                                                                                                   ==> (x₇₀ < 100000
                                                                                                                                                                                                                                       ==> a1₅₂[x₇₀] == a9₆₈[x₇₀]
                                                                                                                                                                                                                                        && (true
                                                                                                                                                                                                                                           ==> true
                                                                                                                                                                                                                                            && 0 <= x₇₀ + 1
                                                                                                                                                                                                                                            && x₇₀ + 1 <= 100000
                                                                                                                                                                                                                                            && (forall x₅₀: int ::
                                                                                                                                                                                                                                                  (  x₅₀ <= x₅₀
                                                                                                                                                                                                                                                    && 0 <= x₅₀
                                                                                                                                                                                                                                                    && x₅₀ < x₇₀ + 1
                                                                                                                                                                                                                                                     ==> x₅₀ < 100000))
                                                                                                                                                                                                                                            && true
                                                                                                                                                                                                                                            && (true
                                                                                                                                                                                                                                               ==> true)))
                                                                                                                                                                                                                                    && (!(x₇₀ < 100000
                                                                                                                                                                                                                                    )
                                                                                                                                                                                                                                       ==> true
                                                                                                                                                                                                                                        && (true
                                                                                                                                                                                                                                           ==> true)))))))))))))))))))))))))))))))))))))))))))))))));


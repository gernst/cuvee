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
                                      true
                                      && 0 <= 0
                                      && 0 <= 100000
                                      && (forall x₁₀: int ::
                                            ((exists a₉: int ::
                                                    x₁₀ == a₉
                                                    && 0 <= a₉
                                                    && a₉ < 0)
                                               ==> (exists __VERIFIER_nondet_int₁₈: int, a₉: int ::
                                                      a₉ < 100000
                                                      && x₁₀ == a₉
                                                      && 0 <= a₉
                                                      && a₉ < 0
                                                      && a1[x₁₀] == __VERIFIER_nondet_int₁₈)))
                                      && (forall x₁₀: int ::
                                            (!((exists a₉: int ::
                                                    x₁₀ == a₉
                                                    && 0 <= a₉
                                                    && a₉ < 0)
                                            )
                                               ==> a1[x₁₀] == a1[x₁₀]))
                                      && (forall a₉: int ::
                                            (  a₉ <= a₉
                                              && 0 <= a₉
                                              && a₉ < 0
                                               ==> a₉ < 100000))
                                      && (forall a1₃₇: [int]int, a₃₈: int ::
                                            (  true
                                              && 0 <= a₃₈
                                              && a₃₈ <= 100000
                                              && (forall x₁₀: int ::
                                                    ((exists a₉: int ::
                                                            x₁₀ == a₉
                                                            && 0 <= a₉
                                                            && a₉ < a₃₈)
                                                       ==> (exists __VERIFIER_nondet_int₁₈: int, a₉: int ::
                                                              a₉ < 100000
                                                              && x₁₀ == a₉
                                                              && 0 <= a₉
                                                              && a₉ < a₃₈
                                                              && a1₃₇[x₁₀] == __VERIFIER_nondet_int₁₈)))
                                              && (forall x₁₀: int ::
                                                    (!((exists a₉: int ::
                                                            x₁₀ == a₉
                                                            && 0 <= a₉
                                                            && a₉ < a₃₈)
                                                    )
                                                       ==> a1₃₇[x₁₀] == a1[x₁₀]))
                                              && (forall a₉: int ::
                                                    (  a₉ <= a₉
                                                      && 0 <= a₉
                                                      && a₉ < a₃₈
                                                       ==> a₉ < 100000))
                                               ==> (a₃₈ < 100000
                                                   ==> (forall __VERIFIER_nondet_int₁: int ::
                                                          true
                                                          && 0 <= a₃₈ + 1
                                                          && a₃₈ + 1 <= 100000
                                                          && (forall x₁₀: int ::
                                                                ((exists a₉: int ::
                                                                        x₁₀ == a₉
                                                                        && 0 <= a₉
                                                                        && a₉ < a₃₈ + 1)
                                                                   ==> (exists __VERIFIER_nondet_int₁₈: int, a₉: int ::
                                                                          a₉ < 100000
                                                                          && x₁₀ == a₉
                                                                          && 0 <= a₉
                                                                          && a₉ < a₃₈ + 1
                                                                          && a1₃₇[a₃₈ := __VERIFIER_nondet_int₁][x₁₀] == __VERIFIER_nondet_int₁₈)))
                                                          && (forall x₁₀: int ::
                                                                (!((exists a₉: int ::
                                                                        x₁₀ == a₉
                                                                        && 0 <= a₉
                                                                        && a₉ < a₃₈ + 1)
                                                                )
                                                                   ==> a1₃₇[a₃₈ := __VERIFIER_nondet_int₁][x₁₀] == a1[x₁₀]))
                                                          && (forall a₉: int ::
                                                                (  a₉ <= a₉
                                                                  && 0 <= a₉
                                                                  && a₉ < a₃₈ + 1
                                                                   ==> a₉ < 100000))
                                                          && true
                                                          && (true
                                                             ==> true)))
                                                && (!(a₃₈ < 100000
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> true
                                                        && 0 <= 0
                                                        && 0 <= 100000
                                                        && (forall x₁₅: int ::
                                                              ((exists i₁₄: int ::
                                                                      x₁₅ == i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < 0)
                                                                 ==> (exists i₁₄: int ::
                                                                        i₁₄ < 100000
                                                                        && x₁₅ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < 0
                                                                        && a2[x₁₅] == a1₃₇[i₁₄])))
                                                        && (forall x₁₅: int ::
                                                              (!((exists i₁₄: int ::
                                                                      x₁₅ == i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < 0)
                                                              )
                                                                 ==> a2[x₁₅] == a2[x₁₅]))
                                                        && (forall i₁₄: int ::
                                                              (  i₁₄ <= i₁₄
                                                                && 0 <= i₁₄
                                                                && i₁₄ < 0
                                                                 ==> i₁₄ < 100000))
                                                        && (forall a2₃₉: [int]int, i₄₀: int ::
                                                              (  true
                                                                && 0 <= i₄₀
                                                                && i₄₀ <= 100000
                                                                && (forall x₁₅: int ::
                                                                      ((exists i₁₄: int ::
                                                                              x₁₅ == i₁₄
                                                                              && 0 <= i₁₄
                                                                              && i₁₄ < i₄₀)
                                                                         ==> (exists i₁₄: int ::
                                                                                i₁₄ < 100000
                                                                                && x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₄₀
                                                                                && a2₃₉[x₁₅] == a1₃₇[i₁₄])))
                                                                && (forall x₁₅: int ::
                                                                      (!((exists i₁₄: int ::
                                                                              x₁₅ == i₁₄
                                                                              && 0 <= i₁₄
                                                                              && i₁₄ < i₄₀)
                                                                      )
                                                                         ==> a2₃₉[x₁₅] == a2[x₁₅]))
                                                                && (forall i₁₄: int ::
                                                                      (  i₁₄ <= i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₄₀
                                                                         ==> i₁₄ < 100000))
                                                                 ==> (i₄₀ < 100000
                                                                     ==> true
                                                                      && 0 <= i₄₀ + 1
                                                                      && i₄₀ + 1 <= 100000
                                                                      && (forall x₁₅: int ::
                                                                            ((exists i₁₄: int ::
                                                                                    x₁₅ == i₁₄
                                                                                    && 0 <= i₁₄
                                                                                    && i₁₄ < i₄₀ + 1)
                                                                               ==> (exists i₁₄: int ::
                                                                                      i₁₄ < 100000
                                                                                      && x₁₅ == i₁₄
                                                                                      && 0 <= i₁₄
                                                                                      && i₁₄ < i₄₀ + 1
                                                                                      && a2₃₉[i₄₀ := a1₃₇[i₄₀]][x₁₅] == a1₃₇[i₁₄])))
                                                                      && (forall x₁₅: int ::
                                                                            (!((exists i₁₄: int ::
                                                                                    x₁₅ == i₁₄
                                                                                    && 0 <= i₁₄
                                                                                    && i₁₄ < i₄₀ + 1)
                                                                            )
                                                                               ==> a2₃₉[i₄₀ := a1₃₇[i₄₀]][x₁₅] == a2[x₁₅]))
                                                                      && (forall i₁₄: int ::
                                                                            (  i₁₄ <= i₁₄
                                                                              && 0 <= i₁₄
                                                                              && i₁₄ < i₄₀ + 1
                                                                               ==> i₁₄ < 100000))
                                                                      && true
                                                                      && (true
                                                                         ==> true))
                                                                  && (!(i₄₀ < 100000
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true
                                                                          && 0 <= 0
                                                                          && 0 <= 100000
                                                                          && (forall x₁₉: int ::
                                                                                ((exists i₁₈: int ::
                                                                                        x₁₉ == i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < 0)
                                                                                   ==> (exists i₁₈: int ::
                                                                                          i₁₈ < 100000
                                                                                          && x₁₉ == i₁₈
                                                                                          && 0 <= i₁₈
                                                                                          && i₁₈ < 0
                                                                                          && a3[x₁₉] == a2₃₉[i₁₈])))
                                                                          && (forall x₁₉: int ::
                                                                                (!((exists i₁₈: int ::
                                                                                        x₁₉ == i₁₈
                                                                                        && 0 <= i₁₈
                                                                                        && i₁₈ < 0)
                                                                                )
                                                                                   ==> a3[x₁₉] == a3[x₁₉]))
                                                                          && (forall i₁₈: int ::
                                                                                (  i₁₈ <= i₁₈
                                                                                  && 0 <= i₁₈
                                                                                  && i₁₈ < 0
                                                                                   ==> i₁₈ < 100000))
                                                                          && (forall a3₄₁: [int]int, i₄₂: int ::
                                                                                (  true
                                                                                  && 0 <= i₄₂
                                                                                  && i₄₂ <= 100000
                                                                                  && (forall x₁₉: int ::
                                                                                        ((exists i₁₈: int ::
                                                                                                x₁₉ == i₁₈
                                                                                                && 0 <= i₁₈
                                                                                                && i₁₈ < i₄₂)
                                                                                           ==> (exists i₁₈: int ::
                                                                                                  i₁₈ < 100000
                                                                                                  && x₁₉ == i₁₈
                                                                                                  && 0 <= i₁₈
                                                                                                  && i₁₈ < i₄₂
                                                                                                  && a3₄₁[x₁₉] == a2₃₉[i₁₈])))
                                                                                  && (forall x₁₉: int ::
                                                                                        (!((exists i₁₈: int ::
                                                                                                x₁₉ == i₁₈
                                                                                                && 0 <= i₁₈
                                                                                                && i₁₈ < i₄₂)
                                                                                        )
                                                                                           ==> a3₄₁[x₁₉] == a3[x₁₉]))
                                                                                  && (forall i₁₈: int ::
                                                                                        (  i₁₈ <= i₁₈
                                                                                          && 0 <= i₁₈
                                                                                          && i₁₈ < i₄₂
                                                                                           ==> i₁₈ < 100000))
                                                                                   ==> (i₄₂ < 100000
                                                                                       ==> true
                                                                                        && 0 <= i₄₂ + 1
                                                                                        && i₄₂ + 1 <= 100000
                                                                                        && (forall x₁₉: int ::
                                                                                              ((exists i₁₈: int ::
                                                                                                      x₁₉ == i₁₈
                                                                                                      && 0 <= i₁₈
                                                                                                      && i₁₈ < i₄₂ + 1)
                                                                                                 ==> (exists i₁₈: int ::
                                                                                                        i₁₈ < 100000
                                                                                                        && x₁₉ == i₁₈
                                                                                                        && 0 <= i₁₈
                                                                                                        && i₁₈ < i₄₂ + 1
                                                                                                        && a3₄₁[i₄₂ := a2₃₉[i₄₂]][x₁₉] == a2₃₉[i₁₈])))
                                                                                        && (forall x₁₉: int ::
                                                                                              (!((exists i₁₈: int ::
                                                                                                      x₁₉ == i₁₈
                                                                                                      && 0 <= i₁₈
                                                                                                      && i₁₈ < i₄₂ + 1)
                                                                                              )
                                                                                                 ==> a3₄₁[i₄₂ := a2₃₉[i₄₂]][x₁₉] == a3[x₁₉]))
                                                                                        && (forall i₁₈: int ::
                                                                                              (  i₁₈ <= i₁₈
                                                                                                && 0 <= i₁₈
                                                                                                && i₁₈ < i₄₂ + 1
                                                                                                 ==> i₁₈ < 100000))
                                                                                        && true
                                                                                        && (true
                                                                                           ==> true))
                                                                                    && (!(i₄₂ < 100000
                                                                                    )
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 0 <= 0
                                                                                            && 0 <= 100000
                                                                                            && (forall x₂₃: int ::
                                                                                                  ((exists i₂₂: int ::
                                                                                                          x₂₃ == i₂₂
                                                                                                          && 0 <= i₂₂
                                                                                                          && i₂₂ < 0)
                                                                                                     ==> (exists i₂₂: int ::
                                                                                                            i₂₂ < 100000
                                                                                                            && x₂₃ == i₂₂
                                                                                                            && 0 <= i₂₂
                                                                                                            && i₂₂ < 0
                                                                                                            && a4[x₂₃] == a3₄₁[i₂₂])))
                                                                                            && (forall x₂₃: int ::
                                                                                                  (!((exists i₂₂: int ::
                                                                                                          x₂₃ == i₂₂
                                                                                                          && 0 <= i₂₂
                                                                                                          && i₂₂ < 0)
                                                                                                  )
                                                                                                     ==> a4[x₂₃] == a4[x₂₃]))
                                                                                            && (forall i₂₂: int ::
                                                                                                  (  i₂₂ <= i₂₂
                                                                                                    && 0 <= i₂₂
                                                                                                    && i₂₂ < 0
                                                                                                     ==> i₂₂ < 100000))
                                                                                            && (forall a4₄₃: [int]int, i₄₄: int ::
                                                                                                  (  true
                                                                                                    && 0 <= i₄₄
                                                                                                    && i₄₄ <= 100000
                                                                                                    && (forall x₂₃: int ::
                                                                                                          ((exists i₂₂: int ::
                                                                                                                  x₂₃ == i₂₂
                                                                                                                  && 0 <= i₂₂
                                                                                                                  && i₂₂ < i₄₄)
                                                                                                             ==> (exists i₂₂: int ::
                                                                                                                    i₂₂ < 100000
                                                                                                                    && x₂₃ == i₂₂
                                                                                                                    && 0 <= i₂₂
                                                                                                                    && i₂₂ < i₄₄
                                                                                                                    && a4₄₃[x₂₃] == a3₄₁[i₂₂])))
                                                                                                    && (forall x₂₃: int ::
                                                                                                          (!((exists i₂₂: int ::
                                                                                                                  x₂₃ == i₂₂
                                                                                                                  && 0 <= i₂₂
                                                                                                                  && i₂₂ < i₄₄)
                                                                                                          )
                                                                                                             ==> a4₄₃[x₂₃] == a4[x₂₃]))
                                                                                                    && (forall i₂₂: int ::
                                                                                                          (  i₂₂ <= i₂₂
                                                                                                            && 0 <= i₂₂
                                                                                                            && i₂₂ < i₄₄
                                                                                                             ==> i₂₂ < 100000))
                                                                                                     ==> (i₄₄ < 100000
                                                                                                         ==> true
                                                                                                          && 0 <= i₄₄ + 1
                                                                                                          && i₄₄ + 1 <= 100000
                                                                                                          && (forall x₂₃: int ::
                                                                                                                ((exists i₂₂: int ::
                                                                                                                        x₂₃ == i₂₂
                                                                                                                        && 0 <= i₂₂
                                                                                                                        && i₂₂ < i₄₄ + 1)
                                                                                                                   ==> (exists i₂₂: int ::
                                                                                                                          i₂₂ < 100000
                                                                                                                          && x₂₃ == i₂₂
                                                                                                                          && 0 <= i₂₂
                                                                                                                          && i₂₂ < i₄₄ + 1
                                                                                                                          && a4₄₃[i₄₄ := a3₄₁[i₄₄]][x₂₃] == a3₄₁[i₂₂])))
                                                                                                          && (forall x₂₃: int ::
                                                                                                                (!((exists i₂₂: int ::
                                                                                                                        x₂₃ == i₂₂
                                                                                                                        && 0 <= i₂₂
                                                                                                                        && i₂₂ < i₄₄ + 1)
                                                                                                                )
                                                                                                                   ==> a4₄₃[i₄₄ := a3₄₁[i₄₄]][x₂₃] == a4[x₂₃]))
                                                                                                          && (forall i₂₂: int ::
                                                                                                                (  i₂₂ <= i₂₂
                                                                                                                  && 0 <= i₂₂
                                                                                                                  && i₂₂ < i₄₄ + 1
                                                                                                                   ==> i₂₂ < 100000))
                                                                                                          && true
                                                                                                          && (true
                                                                                                             ==> true))
                                                                                                      && (!(i₄₄ < 100000
                                                                                                      )
                                                                                                         ==> true
                                                                                                          && (true
                                                                                                             ==> true
                                                                                                              && 0 <= 0
                                                                                                              && 0 <= 100000
                                                                                                              && (forall x₂₇: int ::
                                                                                                                    ((exists i₂₆: int ::
                                                                                                                            x₂₇ == i₂₆
                                                                                                                            && 0 <= i₂₆
                                                                                                                            && i₂₆ < 0)
                                                                                                                       ==> (exists i₂₆: int ::
                                                                                                                              i₂₆ < 100000
                                                                                                                              && x₂₇ == i₂₆
                                                                                                                              && 0 <= i₂₆
                                                                                                                              && i₂₆ < 0
                                                                                                                              && a5[x₂₇] == a4₄₃[i₂₆])))
                                                                                                              && (forall x₂₇: int ::
                                                                                                                    (!((exists i₂₆: int ::
                                                                                                                            x₂₇ == i₂₆
                                                                                                                            && 0 <= i₂₆
                                                                                                                            && i₂₆ < 0)
                                                                                                                    )
                                                                                                                       ==> a5[x₂₇] == a5[x₂₇]))
                                                                                                              && (forall i₂₆: int ::
                                                                                                                    (  i₂₆ <= i₂₆
                                                                                                                      && 0 <= i₂₆
                                                                                                                      && i₂₆ < 0
                                                                                                                       ==> i₂₆ < 100000))
                                                                                                              && (forall a5₄₅: [int]int, i₄₆: int ::
                                                                                                                    (  true
                                                                                                                      && 0 <= i₄₆
                                                                                                                      && i₄₆ <= 100000
                                                                                                                      && (forall x₂₇: int ::
                                                                                                                            ((exists i₂₆: int ::
                                                                                                                                    x₂₇ == i₂₆
                                                                                                                                    && 0 <= i₂₆
                                                                                                                                    && i₂₆ < i₄₆)
                                                                                                                               ==> (exists i₂₆: int ::
                                                                                                                                      i₂₆ < 100000
                                                                                                                                      && x₂₇ == i₂₆
                                                                                                                                      && 0 <= i₂₆
                                                                                                                                      && i₂₆ < i₄₆
                                                                                                                                      && a5₄₅[x₂₇] == a4₄₃[i₂₆])))
                                                                                                                      && (forall x₂₇: int ::
                                                                                                                            (!((exists i₂₆: int ::
                                                                                                                                    x₂₇ == i₂₆
                                                                                                                                    && 0 <= i₂₆
                                                                                                                                    && i₂₆ < i₄₆)
                                                                                                                            )
                                                                                                                               ==> a5₄₅[x₂₇] == a5[x₂₇]))
                                                                                                                      && (forall i₂₆: int ::
                                                                                                                            (  i₂₆ <= i₂₆
                                                                                                                              && 0 <= i₂₆
                                                                                                                              && i₂₆ < i₄₆
                                                                                                                               ==> i₂₆ < 100000))
                                                                                                                       ==> (i₄₆ < 100000
                                                                                                                           ==> true
                                                                                                                            && 0 <= i₄₆ + 1
                                                                                                                            && i₄₆ + 1 <= 100000
                                                                                                                            && (forall x₂₇: int ::
                                                                                                                                  ((exists i₂₆: int ::
                                                                                                                                          x₂₇ == i₂₆
                                                                                                                                          && 0 <= i₂₆
                                                                                                                                          && i₂₆ < i₄₆ + 1)
                                                                                                                                     ==> (exists i₂₆: int ::
                                                                                                                                            i₂₆ < 100000
                                                                                                                                            && x₂₇ == i₂₆
                                                                                                                                            && 0 <= i₂₆
                                                                                                                                            && i₂₆ < i₄₆ + 1
                                                                                                                                            && a5₄₅[i₄₆ := a4₄₃[i₄₆]][x₂₇] == a4₄₃[i₂₆])))
                                                                                                                            && (forall x₂₇: int ::
                                                                                                                                  (!((exists i₂₆: int ::
                                                                                                                                          x₂₇ == i₂₆
                                                                                                                                          && 0 <= i₂₆
                                                                                                                                          && i₂₆ < i₄₆ + 1)
                                                                                                                                  )
                                                                                                                                     ==> a5₄₅[i₄₆ := a4₄₃[i₄₆]][x₂₇] == a5[x₂₇]))
                                                                                                                            && (forall i₂₆: int ::
                                                                                                                                  (  i₂₆ <= i₂₆
                                                                                                                                    && 0 <= i₂₆
                                                                                                                                    && i₂₆ < i₄₆ + 1
                                                                                                                                     ==> i₂₆ < 100000))
                                                                                                                            && true
                                                                                                                            && (true
                                                                                                                               ==> true))
                                                                                                                        && (!(i₄₆ < 100000
                                                                                                                        )
                                                                                                                           ==> true
                                                                                                                            && (true
                                                                                                                               ==> true
                                                                                                                                && 0 <= 0
                                                                                                                                && 0 <= 100000
                                                                                                                                && (forall x₃₁: int ::
                                                                                                                                      ((exists i₃₀: int ::
                                                                                                                                              x₃₁ == i₃₀
                                                                                                                                              && 0 <= i₃₀
                                                                                                                                              && i₃₀ < 0)
                                                                                                                                         ==> (exists i₃₀: int ::
                                                                                                                                                i₃₀ < 100000
                                                                                                                                                && x₃₁ == i₃₀
                                                                                                                                                && 0 <= i₃₀
                                                                                                                                                && i₃₀ < 0
                                                                                                                                                && a6[x₃₁] == a5₄₅[i₃₀])))
                                                                                                                                && (forall x₃₁: int ::
                                                                                                                                      (!((exists i₃₀: int ::
                                                                                                                                              x₃₁ == i₃₀
                                                                                                                                              && 0 <= i₃₀
                                                                                                                                              && i₃₀ < 0)
                                                                                                                                      )
                                                                                                                                         ==> a6[x₃₁] == a6[x₃₁]))
                                                                                                                                && (forall i₃₀: int ::
                                                                                                                                      (  i₃₀ <= i₃₀
                                                                                                                                        && 0 <= i₃₀
                                                                                                                                        && i₃₀ < 0
                                                                                                                                         ==> i₃₀ < 100000))
                                                                                                                                && (forall a6₄₇: [int]int, i₄₈: int ::
                                                                                                                                      (  true
                                                                                                                                        && 0 <= i₄₈
                                                                                                                                        && i₄₈ <= 100000
                                                                                                                                        && (forall x₃₁: int ::
                                                                                                                                              ((exists i₃₀: int ::
                                                                                                                                                      x₃₁ == i₃₀
                                                                                                                                                      && 0 <= i₃₀
                                                                                                                                                      && i₃₀ < i₄₈)
                                                                                                                                                 ==> (exists i₃₀: int ::
                                                                                                                                                        i₃₀ < 100000
                                                                                                                                                        && x₃₁ == i₃₀
                                                                                                                                                        && 0 <= i₃₀
                                                                                                                                                        && i₃₀ < i₄₈
                                                                                                                                                        && a6₄₇[x₃₁] == a5₄₅[i₃₀])))
                                                                                                                                        && (forall x₃₁: int ::
                                                                                                                                              (!((exists i₃₀: int ::
                                                                                                                                                      x₃₁ == i₃₀
                                                                                                                                                      && 0 <= i₃₀
                                                                                                                                                      && i₃₀ < i₄₈)
                                                                                                                                              )
                                                                                                                                                 ==> a6₄₇[x₃₁] == a6[x₃₁]))
                                                                                                                                        && (forall i₃₀: int ::
                                                                                                                                              (  i₃₀ <= i₃₀
                                                                                                                                                && 0 <= i₃₀
                                                                                                                                                && i₃₀ < i₄₈
                                                                                                                                                 ==> i₃₀ < 100000))
                                                                                                                                         ==> (i₄₈ < 100000
                                                                                                                                             ==> true
                                                                                                                                              && 0 <= i₄₈ + 1
                                                                                                                                              && i₄₈ + 1 <= 100000
                                                                                                                                              && (forall x₃₁: int ::
                                                                                                                                                    ((exists i₃₀: int ::
                                                                                                                                                            x₃₁ == i₃₀
                                                                                                                                                            && 0 <= i₃₀
                                                                                                                                                            && i₃₀ < i₄₈ + 1)
                                                                                                                                                       ==> (exists i₃₀: int ::
                                                                                                                                                              i₃₀ < 100000
                                                                                                                                                              && x₃₁ == i₃₀
                                                                                                                                                              && 0 <= i₃₀
                                                                                                                                                              && i₃₀ < i₄₈ + 1
                                                                                                                                                              && a6₄₇[i₄₈ := a5₄₅[i₄₈]][x₃₁] == a5₄₅[i₃₀])))
                                                                                                                                              && (forall x₃₁: int ::
                                                                                                                                                    (!((exists i₃₀: int ::
                                                                                                                                                            x₃₁ == i₃₀
                                                                                                                                                            && 0 <= i₃₀
                                                                                                                                                            && i₃₀ < i₄₈ + 1)
                                                                                                                                                    )
                                                                                                                                                       ==> a6₄₇[i₄₈ := a5₄₅[i₄₈]][x₃₁] == a6[x₃₁]))
                                                                                                                                              && (forall i₃₀: int ::
                                                                                                                                                    (  i₃₀ <= i₃₀
                                                                                                                                                      && 0 <= i₃₀
                                                                                                                                                      && i₃₀ < i₄₈ + 1
                                                                                                                                                       ==> i₃₀ < 100000))
                                                                                                                                              && true
                                                                                                                                              && (true
                                                                                                                                                 ==> true))
                                                                                                                                          && (!(i₄₈ < 100000
                                                                                                                                          )
                                                                                                                                             ==> true
                                                                                                                                              && (true
                                                                                                                                                 ==> true
                                                                                                                                                  && 0 <= 0
                                                                                                                                                  && 0 <= 100000
                                                                                                                                                  && (forall x₃₅: int ::
                                                                                                                                                        (  x₃₅ <= x₃₅
                                                                                                                                                          && 0 <= x₃₅
                                                                                                                                                          && x₃₅ < 0
                                                                                                                                                           ==> x₃₅ < 100000))
                                                                                                                                                  && (forall x₄₉: int ::
                                                                                                                                                        (  true
                                                                                                                                                          && 0 <= x₄₉
                                                                                                                                                          && x₄₉ <= 100000
                                                                                                                                                          && (forall x₃₅: int ::
                                                                                                                                                                (  x₃₅ <= x₃₅
                                                                                                                                                                  && 0 <= x₃₅
                                                                                                                                                                  && x₃₅ < x₄₉
                                                                                                                                                                   ==> x₃₅ < 100000))
                                                                                                                                                           ==> (x₄₉ < 100000
                                                                                                                                                               ==> a1₃₇[x₄₉] == a6₄₇[x₄₉]
                                                                                                                                                                && (true
                                                                                                                                                                   ==> true
                                                                                                                                                                    && 0 <= x₄₉ + 1
                                                                                                                                                                    && x₄₉ + 1 <= 100000
                                                                                                                                                                    && (forall x₃₅: int ::
                                                                                                                                                                          (  x₃₅ <= x₃₅
                                                                                                                                                                            && 0 <= x₃₅
                                                                                                                                                                            && x₃₅ < x₄₉ + 1
                                                                                                                                                                             ==> x₃₅ < 100000))
                                                                                                                                                                    && true
                                                                                                                                                                    && (true
                                                                                                                                                                       ==> true)))
                                                                                                                                                            && (!(x₄₉ < 100000
                                                                                                                                                            )
                                                                                                                                                               ==> true
                                                                                                                                                                && (true
                                                                                                                                                                   ==> true))))))))))))))))))))))))))))))))));


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
                                                  true
                                                  && 0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₁₂: int ::
                                                        ((exists a₁₁: int ::
                                                                x₁₂ == a₁₁
                                                                && 0 <= a₁₁
                                                                && a₁₁ < 0)
                                                           ==> (exists __VERIFIER_nondet_int₁₁₀: int, a₁₁: int ::
                                                                  a₁₁ < 100000
                                                                  && x₁₂ == a₁₁
                                                                  && 0 <= a₁₁
                                                                  && a₁₁ < 0
                                                                  && a1[x₁₂] == __VERIFIER_nondet_int₁₁₀)))
                                                  && (forall x₁₂: int ::
                                                        (!((exists a₁₁: int ::
                                                                x₁₂ == a₁₁
                                                                && 0 <= a₁₁
                                                                && a₁₁ < 0)
                                                        )
                                                           ==> a1[x₁₂] == a1[x₁₂]))
                                                  && (forall a₁₁: int ::
                                                        (  a₁₁ <= a₁₁
                                                          && 0 <= a₁₁
                                                          && a₁₁ < 0
                                                           ==> a₁₁ < 100000))
                                                  && (forall a1₄₇: [int]int, a₄₈: int ::
                                                        (  true
                                                          && 0 <= a₄₈
                                                          && a₄₈ <= 100000
                                                          && (forall x₁₂: int ::
                                                                ((exists a₁₁: int ::
                                                                        x₁₂ == a₁₁
                                                                        && 0 <= a₁₁
                                                                        && a₁₁ < a₄₈)
                                                                   ==> (exists __VERIFIER_nondet_int₁₁₀: int, a₁₁: int ::
                                                                          a₁₁ < 100000
                                                                          && x₁₂ == a₁₁
                                                                          && 0 <= a₁₁
                                                                          && a₁₁ < a₄₈
                                                                          && a1₄₇[x₁₂] == __VERIFIER_nondet_int₁₁₀)))
                                                          && (forall x₁₂: int ::
                                                                (!((exists a₁₁: int ::
                                                                        x₁₂ == a₁₁
                                                                        && 0 <= a₁₁
                                                                        && a₁₁ < a₄₈)
                                                                )
                                                                   ==> a1₄₇[x₁₂] == a1[x₁₂]))
                                                          && (forall a₁₁: int ::
                                                                (  a₁₁ <= a₁₁
                                                                  && 0 <= a₁₁
                                                                  && a₁₁ < a₄₈
                                                                   ==> a₁₁ < 100000))
                                                           ==> (a₄₈ < 100000
                                                               ==> (forall __VERIFIER_nondet_int₁: int ::
                                                                      true
                                                                      && 0 <= a₄₈ + 1
                                                                      && a₄₈ + 1 <= 100000
                                                                      && (forall x₁₂: int ::
                                                                            ((exists a₁₁: int ::
                                                                                    x₁₂ == a₁₁
                                                                                    && 0 <= a₁₁
                                                                                    && a₁₁ < a₄₈ + 1)
                                                                               ==> (exists __VERIFIER_nondet_int₁₁₀: int, a₁₁: int ::
                                                                                      a₁₁ < 100000
                                                                                      && x₁₂ == a₁₁
                                                                                      && 0 <= a₁₁
                                                                                      && a₁₁ < a₄₈ + 1
                                                                                      && a1₄₇[a₄₈ := __VERIFIER_nondet_int₁][x₁₂] == __VERIFIER_nondet_int₁₁₀)))
                                                                      && (forall x₁₂: int ::
                                                                            (!((exists a₁₁: int ::
                                                                                    x₁₂ == a₁₁
                                                                                    && 0 <= a₁₁
                                                                                    && a₁₁ < a₄₈ + 1)
                                                                            )
                                                                               ==> a1₄₇[a₄₈ := __VERIFIER_nondet_int₁][x₁₂] == a1[x₁₂]))
                                                                      && (forall a₁₁: int ::
                                                                            (  a₁₁ <= a₁₁
                                                                              && 0 <= a₁₁
                                                                              && a₁₁ < a₄₈ + 1
                                                                               ==> a₁₁ < 100000))
                                                                      && true
                                                                      && (true
                                                                         ==> true)))
                                                            && (!(a₄₈ < 100000
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
                                                                                    && a2[x₁₇] == a1₄₇[i₁₆])))
                                                                    && (forall x₁₇: int ::
                                                                          (!((exists i₁₆: int ::
                                                                                  x₁₇ == i₁₆
                                                                                  && 0 <= i₁₆
                                                                                  && i₁₆ < 0)
                                                                          )
                                                                             ==> a2[x₁₇] == a2[x₁₇]))
                                                                    && (forall i₁₆: int ::
                                                                          (  i₁₆ <= i₁₆
                                                                            && 0 <= i₁₆
                                                                            && i₁₆ < 0
                                                                             ==> i₁₆ < 100000))
                                                                    && (forall a2₄₉: [int]int, i₅₀: int ::
                                                                          (  true
                                                                            && 0 <= i₅₀
                                                                            && i₅₀ <= 100000
                                                                            && (forall x₁₇: int ::
                                                                                  ((exists i₁₆: int ::
                                                                                          x₁₇ == i₁₆
                                                                                          && 0 <= i₁₆
                                                                                          && i₁₆ < i₅₀)
                                                                                     ==> (exists i₁₆: int ::
                                                                                            i₁₆ < 100000
                                                                                            && x₁₇ == i₁₆
                                                                                            && 0 <= i₁₆
                                                                                            && i₁₆ < i₅₀
                                                                                            && a2₄₉[x₁₇] == a1₄₇[i₁₆])))
                                                                            && (forall x₁₇: int ::
                                                                                  (!((exists i₁₆: int ::
                                                                                          x₁₇ == i₁₆
                                                                                          && 0 <= i₁₆
                                                                                          && i₁₆ < i₅₀)
                                                                                  )
                                                                                     ==> a2₄₉[x₁₇] == a2[x₁₇]))
                                                                            && (forall i₁₆: int ::
                                                                                  (  i₁₆ <= i₁₆
                                                                                    && 0 <= i₁₆
                                                                                    && i₁₆ < i₅₀
                                                                                     ==> i₁₆ < 100000))
                                                                             ==> (i₅₀ < 100000
                                                                                 ==> true
                                                                                  && 0 <= i₅₀ + 1
                                                                                  && i₅₀ + 1 <= 100000
                                                                                  && (forall x₁₇: int ::
                                                                                        ((exists i₁₆: int ::
                                                                                                x₁₇ == i₁₆
                                                                                                && 0 <= i₁₆
                                                                                                && i₁₆ < i₅₀ + 1)
                                                                                           ==> (exists i₁₆: int ::
                                                                                                  i₁₆ < 100000
                                                                                                  && x₁₇ == i₁₆
                                                                                                  && 0 <= i₁₆
                                                                                                  && i₁₆ < i₅₀ + 1
                                                                                                  && a2₄₉[i₅₀ := a1₄₇[i₅₀]][x₁₇] == a1₄₇[i₁₆])))
                                                                                  && (forall x₁₇: int ::
                                                                                        (!((exists i₁₆: int ::
                                                                                                x₁₇ == i₁₆
                                                                                                && 0 <= i₁₆
                                                                                                && i₁₆ < i₅₀ + 1)
                                                                                        )
                                                                                           ==> a2₄₉[i₅₀ := a1₄₇[i₅₀]][x₁₇] == a2[x₁₇]))
                                                                                  && (forall i₁₆: int ::
                                                                                        (  i₁₆ <= i₁₆
                                                                                          && 0 <= i₁₆
                                                                                          && i₁₆ < i₅₀ + 1
                                                                                           ==> i₁₆ < 100000))
                                                                                  && true
                                                                                  && (true
                                                                                     ==> true))
                                                                              && (!(i₅₀ < 100000
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
                                                                                                      && a3[x₂₁] == a2₄₉[i₂₀])))
                                                                                      && (forall x₂₁: int ::
                                                                                            (!((exists i₂₀: int ::
                                                                                                    x₂₁ == i₂₀
                                                                                                    && 0 <= i₂₀
                                                                                                    && i₂₀ < 0)
                                                                                            )
                                                                                               ==> a3[x₂₁] == a3[x₂₁]))
                                                                                      && (forall i₂₀: int ::
                                                                                            (  i₂₀ <= i₂₀
                                                                                              && 0 <= i₂₀
                                                                                              && i₂₀ < 0
                                                                                               ==> i₂₀ < 100000))
                                                                                      && (forall a3₅₁: [int]int, i₅₂: int ::
                                                                                            (  true
                                                                                              && 0 <= i₅₂
                                                                                              && i₅₂ <= 100000
                                                                                              && (forall x₂₁: int ::
                                                                                                    ((exists i₂₀: int ::
                                                                                                            x₂₁ == i₂₀
                                                                                                            && 0 <= i₂₀
                                                                                                            && i₂₀ < i₅₂)
                                                                                                       ==> (exists i₂₀: int ::
                                                                                                              i₂₀ < 100000
                                                                                                              && x₂₁ == i₂₀
                                                                                                              && 0 <= i₂₀
                                                                                                              && i₂₀ < i₅₂
                                                                                                              && a3₅₁[x₂₁] == a2₄₉[i₂₀])))
                                                                                              && (forall x₂₁: int ::
                                                                                                    (!((exists i₂₀: int ::
                                                                                                            x₂₁ == i₂₀
                                                                                                            && 0 <= i₂₀
                                                                                                            && i₂₀ < i₅₂)
                                                                                                    )
                                                                                                       ==> a3₅₁[x₂₁] == a3[x₂₁]))
                                                                                              && (forall i₂₀: int ::
                                                                                                    (  i₂₀ <= i₂₀
                                                                                                      && 0 <= i₂₀
                                                                                                      && i₂₀ < i₅₂
                                                                                                       ==> i₂₀ < 100000))
                                                                                               ==> (i₅₂ < 100000
                                                                                                   ==> true
                                                                                                    && 0 <= i₅₂ + 1
                                                                                                    && i₅₂ + 1 <= 100000
                                                                                                    && (forall x₂₁: int ::
                                                                                                          ((exists i₂₀: int ::
                                                                                                                  x₂₁ == i₂₀
                                                                                                                  && 0 <= i₂₀
                                                                                                                  && i₂₀ < i₅₂ + 1)
                                                                                                             ==> (exists i₂₀: int ::
                                                                                                                    i₂₀ < 100000
                                                                                                                    && x₂₁ == i₂₀
                                                                                                                    && 0 <= i₂₀
                                                                                                                    && i₂₀ < i₅₂ + 1
                                                                                                                    && a3₅₁[i₅₂ := a2₄₉[i₅₂]][x₂₁] == a2₄₉[i₂₀])))
                                                                                                    && (forall x₂₁: int ::
                                                                                                          (!((exists i₂₀: int ::
                                                                                                                  x₂₁ == i₂₀
                                                                                                                  && 0 <= i₂₀
                                                                                                                  && i₂₀ < i₅₂ + 1)
                                                                                                          )
                                                                                                             ==> a3₅₁[i₅₂ := a2₄₉[i₅₂]][x₂₁] == a3[x₂₁]))
                                                                                                    && (forall i₂₀: int ::
                                                                                                          (  i₂₀ <= i₂₀
                                                                                                            && 0 <= i₂₀
                                                                                                            && i₂₀ < i₅₂ + 1
                                                                                                             ==> i₂₀ < 100000))
                                                                                                    && true
                                                                                                    && (true
                                                                                                       ==> true))
                                                                                                && (!(i₅₂ < 100000
                                                                                                )
                                                                                                   ==> true
                                                                                                    && (true
                                                                                                       ==> true
                                                                                                        && 0 <= 0
                                                                                                        && 0 <= 100000
                                                                                                        && (forall x₂₅: int ::
                                                                                                              ((exists i₂₄: int ::
                                                                                                                      x₂₅ == i₂₄
                                                                                                                      && 0 <= i₂₄
                                                                                                                      && i₂₄ < 0)
                                                                                                                 ==> (exists i₂₄: int ::
                                                                                                                        i₂₄ < 100000
                                                                                                                        && x₂₅ == i₂₄
                                                                                                                        && 0 <= i₂₄
                                                                                                                        && i₂₄ < 0
                                                                                                                        && a4[x₂₅] == a3₅₁[i₂₄])))
                                                                                                        && (forall x₂₅: int ::
                                                                                                              (!((exists i₂₄: int ::
                                                                                                                      x₂₅ == i₂₄
                                                                                                                      && 0 <= i₂₄
                                                                                                                      && i₂₄ < 0)
                                                                                                              )
                                                                                                                 ==> a4[x₂₅] == a4[x₂₅]))
                                                                                                        && (forall i₂₄: int ::
                                                                                                              (  i₂₄ <= i₂₄
                                                                                                                && 0 <= i₂₄
                                                                                                                && i₂₄ < 0
                                                                                                                 ==> i₂₄ < 100000))
                                                                                                        && (forall a4₅₃: [int]int, i₅₄: int ::
                                                                                                              (  true
                                                                                                                && 0 <= i₅₄
                                                                                                                && i₅₄ <= 100000
                                                                                                                && (forall x₂₅: int ::
                                                                                                                      ((exists i₂₄: int ::
                                                                                                                              x₂₅ == i₂₄
                                                                                                                              && 0 <= i₂₄
                                                                                                                              && i₂₄ < i₅₄)
                                                                                                                         ==> (exists i₂₄: int ::
                                                                                                                                i₂₄ < 100000
                                                                                                                                && x₂₅ == i₂₄
                                                                                                                                && 0 <= i₂₄
                                                                                                                                && i₂₄ < i₅₄
                                                                                                                                && a4₅₃[x₂₅] == a3₅₁[i₂₄])))
                                                                                                                && (forall x₂₅: int ::
                                                                                                                      (!((exists i₂₄: int ::
                                                                                                                              x₂₅ == i₂₄
                                                                                                                              && 0 <= i₂₄
                                                                                                                              && i₂₄ < i₅₄)
                                                                                                                      )
                                                                                                                         ==> a4₅₃[x₂₅] == a4[x₂₅]))
                                                                                                                && (forall i₂₄: int ::
                                                                                                                      (  i₂₄ <= i₂₄
                                                                                                                        && 0 <= i₂₄
                                                                                                                        && i₂₄ < i₅₄
                                                                                                                         ==> i₂₄ < 100000))
                                                                                                                 ==> (i₅₄ < 100000
                                                                                                                     ==> true
                                                                                                                      && 0 <= i₅₄ + 1
                                                                                                                      && i₅₄ + 1 <= 100000
                                                                                                                      && (forall x₂₅: int ::
                                                                                                                            ((exists i₂₄: int ::
                                                                                                                                    x₂₅ == i₂₄
                                                                                                                                    && 0 <= i₂₄
                                                                                                                                    && i₂₄ < i₅₄ + 1)
                                                                                                                               ==> (exists i₂₄: int ::
                                                                                                                                      i₂₄ < 100000
                                                                                                                                      && x₂₅ == i₂₄
                                                                                                                                      && 0 <= i₂₄
                                                                                                                                      && i₂₄ < i₅₄ + 1
                                                                                                                                      && a4₅₃[i₅₄ := a3₅₁[i₅₄]][x₂₅] == a3₅₁[i₂₄])))
                                                                                                                      && (forall x₂₅: int ::
                                                                                                                            (!((exists i₂₄: int ::
                                                                                                                                    x₂₅ == i₂₄
                                                                                                                                    && 0 <= i₂₄
                                                                                                                                    && i₂₄ < i₅₄ + 1)
                                                                                                                            )
                                                                                                                               ==> a4₅₃[i₅₄ := a3₅₁[i₅₄]][x₂₅] == a4[x₂₅]))
                                                                                                                      && (forall i₂₄: int ::
                                                                                                                            (  i₂₄ <= i₂₄
                                                                                                                              && 0 <= i₂₄
                                                                                                                              && i₂₄ < i₅₄ + 1
                                                                                                                               ==> i₂₄ < 100000))
                                                                                                                      && true
                                                                                                                      && (true
                                                                                                                         ==> true))
                                                                                                                  && (!(i₅₄ < 100000
                                                                                                                  )
                                                                                                                     ==> true
                                                                                                                      && (true
                                                                                                                         ==> true
                                                                                                                          && 0 <= 0
                                                                                                                          && 0 <= 100000
                                                                                                                          && (forall x₂₉: int ::
                                                                                                                                ((exists i₂₈: int ::
                                                                                                                                        x₂₉ == i₂₈
                                                                                                                                        && 0 <= i₂₈
                                                                                                                                        && i₂₈ < 0)
                                                                                                                                   ==> (exists i₂₈: int ::
                                                                                                                                          i₂₈ < 100000
                                                                                                                                          && x₂₉ == i₂₈
                                                                                                                                          && 0 <= i₂₈
                                                                                                                                          && i₂₈ < 0
                                                                                                                                          && a5[x₂₉] == a4₅₃[i₂₈])))
                                                                                                                          && (forall x₂₉: int ::
                                                                                                                                (!((exists i₂₈: int ::
                                                                                                                                        x₂₉ == i₂₈
                                                                                                                                        && 0 <= i₂₈
                                                                                                                                        && i₂₈ < 0)
                                                                                                                                )
                                                                                                                                   ==> a5[x₂₉] == a5[x₂₉]))
                                                                                                                          && (forall i₂₈: int ::
                                                                                                                                (  i₂₈ <= i₂₈
                                                                                                                                  && 0 <= i₂₈
                                                                                                                                  && i₂₈ < 0
                                                                                                                                   ==> i₂₈ < 100000))
                                                                                                                          && (forall a5₅₅: [int]int, i₅₆: int ::
                                                                                                                                (  true
                                                                                                                                  && 0 <= i₅₆
                                                                                                                                  && i₅₆ <= 100000
                                                                                                                                  && (forall x₂₉: int ::
                                                                                                                                        ((exists i₂₈: int ::
                                                                                                                                                x₂₉ == i₂₈
                                                                                                                                                && 0 <= i₂₈
                                                                                                                                                && i₂₈ < i₅₆)
                                                                                                                                           ==> (exists i₂₈: int ::
                                                                                                                                                  i₂₈ < 100000
                                                                                                                                                  && x₂₉ == i₂₈
                                                                                                                                                  && 0 <= i₂₈
                                                                                                                                                  && i₂₈ < i₅₆
                                                                                                                                                  && a5₅₅[x₂₉] == a4₅₃[i₂₈])))
                                                                                                                                  && (forall x₂₉: int ::
                                                                                                                                        (!((exists i₂₈: int ::
                                                                                                                                                x₂₉ == i₂₈
                                                                                                                                                && 0 <= i₂₈
                                                                                                                                                && i₂₈ < i₅₆)
                                                                                                                                        )
                                                                                                                                           ==> a5₅₅[x₂₉] == a5[x₂₉]))
                                                                                                                                  && (forall i₂₈: int ::
                                                                                                                                        (  i₂₈ <= i₂₈
                                                                                                                                          && 0 <= i₂₈
                                                                                                                                          && i₂₈ < i₅₆
                                                                                                                                           ==> i₂₈ < 100000))
                                                                                                                                   ==> (i₅₆ < 100000
                                                                                                                                       ==> true
                                                                                                                                        && 0 <= i₅₆ + 1
                                                                                                                                        && i₅₆ + 1 <= 100000
                                                                                                                                        && (forall x₂₉: int ::
                                                                                                                                              ((exists i₂₈: int ::
                                                                                                                                                      x₂₉ == i₂₈
                                                                                                                                                      && 0 <= i₂₈
                                                                                                                                                      && i₂₈ < i₅₆ + 1)
                                                                                                                                                 ==> (exists i₂₈: int ::
                                                                                                                                                        i₂₈ < 100000
                                                                                                                                                        && x₂₉ == i₂₈
                                                                                                                                                        && 0 <= i₂₈
                                                                                                                                                        && i₂₈ < i₅₆ + 1
                                                                                                                                                        && a5₅₅[i₅₆ := a4₅₃[i₅₆]][x₂₉] == a4₅₃[i₂₈])))
                                                                                                                                        && (forall x₂₉: int ::
                                                                                                                                              (!((exists i₂₈: int ::
                                                                                                                                                      x₂₉ == i₂₈
                                                                                                                                                      && 0 <= i₂₈
                                                                                                                                                      && i₂₈ < i₅₆ + 1)
                                                                                                                                              )
                                                                                                                                                 ==> a5₅₅[i₅₆ := a4₅₃[i₅₆]][x₂₉] == a5[x₂₉]))
                                                                                                                                        && (forall i₂₈: int ::
                                                                                                                                              (  i₂₈ <= i₂₈
                                                                                                                                                && 0 <= i₂₈
                                                                                                                                                && i₂₈ < i₅₆ + 1
                                                                                                                                                 ==> i₂₈ < 100000))
                                                                                                                                        && true
                                                                                                                                        && (true
                                                                                                                                           ==> true))
                                                                                                                                    && (!(i₅₆ < 100000
                                                                                                                                    )
                                                                                                                                       ==> true
                                                                                                                                        && (true
                                                                                                                                           ==> true
                                                                                                                                            && 0 <= 0
                                                                                                                                            && 0 <= 100000
                                                                                                                                            && (forall x₃₃: int ::
                                                                                                                                                  ((exists i₃₂: int ::
                                                                                                                                                          x₃₃ == i₃₂
                                                                                                                                                          && 0 <= i₃₂
                                                                                                                                                          && i₃₂ < 0)
                                                                                                                                                     ==> (exists i₃₂: int ::
                                                                                                                                                            i₃₂ < 100000
                                                                                                                                                            && x₃₃ == i₃₂
                                                                                                                                                            && 0 <= i₃₂
                                                                                                                                                            && i₃₂ < 0
                                                                                                                                                            && a6[x₃₃] == a5₅₅[i₃₂])))
                                                                                                                                            && (forall x₃₃: int ::
                                                                                                                                                  (!((exists i₃₂: int ::
                                                                                                                                                          x₃₃ == i₃₂
                                                                                                                                                          && 0 <= i₃₂
                                                                                                                                                          && i₃₂ < 0)
                                                                                                                                                  )
                                                                                                                                                     ==> a6[x₃₃] == a6[x₃₃]))
                                                                                                                                            && (forall i₃₂: int ::
                                                                                                                                                  (  i₃₂ <= i₃₂
                                                                                                                                                    && 0 <= i₃₂
                                                                                                                                                    && i₃₂ < 0
                                                                                                                                                     ==> i₃₂ < 100000))
                                                                                                                                            && (forall a6₅₇: [int]int, i₅₈: int ::
                                                                                                                                                  (  true
                                                                                                                                                    && 0 <= i₅₈
                                                                                                                                                    && i₅₈ <= 100000
                                                                                                                                                    && (forall x₃₃: int ::
                                                                                                                                                          ((exists i₃₂: int ::
                                                                                                                                                                  x₃₃ == i₃₂
                                                                                                                                                                  && 0 <= i₃₂
                                                                                                                                                                  && i₃₂ < i₅₈)
                                                                                                                                                             ==> (exists i₃₂: int ::
                                                                                                                                                                    i₃₂ < 100000
                                                                                                                                                                    && x₃₃ == i₃₂
                                                                                                                                                                    && 0 <= i₃₂
                                                                                                                                                                    && i₃₂ < i₅₈
                                                                                                                                                                    && a6₅₇[x₃₃] == a5₅₅[i₃₂])))
                                                                                                                                                    && (forall x₃₃: int ::
                                                                                                                                                          (!((exists i₃₂: int ::
                                                                                                                                                                  x₃₃ == i₃₂
                                                                                                                                                                  && 0 <= i₃₂
                                                                                                                                                                  && i₃₂ < i₅₈)
                                                                                                                                                          )
                                                                                                                                                             ==> a6₅₇[x₃₃] == a6[x₃₃]))
                                                                                                                                                    && (forall i₃₂: int ::
                                                                                                                                                          (  i₃₂ <= i₃₂
                                                                                                                                                            && 0 <= i₃₂
                                                                                                                                                            && i₃₂ < i₅₈
                                                                                                                                                             ==> i₃₂ < 100000))
                                                                                                                                                     ==> (i₅₈ < 100000
                                                                                                                                                         ==> true
                                                                                                                                                          && 0 <= i₅₈ + 1
                                                                                                                                                          && i₅₈ + 1 <= 100000
                                                                                                                                                          && (forall x₃₃: int ::
                                                                                                                                                                ((exists i₃₂: int ::
                                                                                                                                                                        x₃₃ == i₃₂
                                                                                                                                                                        && 0 <= i₃₂
                                                                                                                                                                        && i₃₂ < i₅₈ + 1)
                                                                                                                                                                   ==> (exists i₃₂: int ::
                                                                                                                                                                          i₃₂ < 100000
                                                                                                                                                                          && x₃₃ == i₃₂
                                                                                                                                                                          && 0 <= i₃₂
                                                                                                                                                                          && i₃₂ < i₅₈ + 1
                                                                                                                                                                          && a6₅₇[i₅₈ := a5₅₅[i₅₈]][x₃₃] == a5₅₅[i₃₂])))
                                                                                                                                                          && (forall x₃₃: int ::
                                                                                                                                                                (!((exists i₃₂: int ::
                                                                                                                                                                        x₃₃ == i₃₂
                                                                                                                                                                        && 0 <= i₃₂
                                                                                                                                                                        && i₃₂ < i₅₈ + 1)
                                                                                                                                                                )
                                                                                                                                                                   ==> a6₅₇[i₅₈ := a5₅₅[i₅₈]][x₃₃] == a6[x₃₃]))
                                                                                                                                                          && (forall i₃₂: int ::
                                                                                                                                                                (  i₃₂ <= i₃₂
                                                                                                                                                                  && 0 <= i₃₂
                                                                                                                                                                  && i₃₂ < i₅₈ + 1
                                                                                                                                                                   ==> i₃₂ < 100000))
                                                                                                                                                          && true
                                                                                                                                                          && (true
                                                                                                                                                             ==> true))
                                                                                                                                                      && (!(i₅₈ < 100000
                                                                                                                                                      )
                                                                                                                                                         ==> true
                                                                                                                                                          && (true
                                                                                                                                                             ==> true
                                                                                                                                                              && 0 <= 0
                                                                                                                                                              && 0 <= 100000
                                                                                                                                                              && (forall x₃₇: int ::
                                                                                                                                                                    ((exists i₃₆: int ::
                                                                                                                                                                            x₃₇ == i₃₆
                                                                                                                                                                            && 0 <= i₃₆
                                                                                                                                                                            && i₃₆ < 0)
                                                                                                                                                                       ==> (exists i₃₆: int ::
                                                                                                                                                                              i₃₆ < 100000
                                                                                                                                                                              && x₃₇ == i₃₆
                                                                                                                                                                              && 0 <= i₃₆
                                                                                                                                                                              && i₃₆ < 0
                                                                                                                                                                              && a7[x₃₇] == a6₅₇[i₃₆])))
                                                                                                                                                              && (forall x₃₇: int ::
                                                                                                                                                                    (!((exists i₃₆: int ::
                                                                                                                                                                            x₃₇ == i₃₆
                                                                                                                                                                            && 0 <= i₃₆
                                                                                                                                                                            && i₃₆ < 0)
                                                                                                                                                                    )
                                                                                                                                                                       ==> a7[x₃₇] == a7[x₃₇]))
                                                                                                                                                              && (forall i₃₆: int ::
                                                                                                                                                                    (  i₃₆ <= i₃₆
                                                                                                                                                                      && 0 <= i₃₆
                                                                                                                                                                      && i₃₆ < 0
                                                                                                                                                                       ==> i₃₆ < 100000))
                                                                                                                                                              && (forall a7₅₉: [int]int, i₆₀: int ::
                                                                                                                                                                    (  true
                                                                                                                                                                      && 0 <= i₆₀
                                                                                                                                                                      && i₆₀ <= 100000
                                                                                                                                                                      && (forall x₃₇: int ::
                                                                                                                                                                            ((exists i₃₆: int ::
                                                                                                                                                                                    x₃₇ == i₃₆
                                                                                                                                                                                    && 0 <= i₃₆
                                                                                                                                                                                    && i₃₆ < i₆₀)
                                                                                                                                                                               ==> (exists i₃₆: int ::
                                                                                                                                                                                      i₃₆ < 100000
                                                                                                                                                                                      && x₃₇ == i₃₆
                                                                                                                                                                                      && 0 <= i₃₆
                                                                                                                                                                                      && i₃₆ < i₆₀
                                                                                                                                                                                      && a7₅₉[x₃₇] == a6₅₇[i₃₆])))
                                                                                                                                                                      && (forall x₃₇: int ::
                                                                                                                                                                            (!((exists i₃₆: int ::
                                                                                                                                                                                    x₃₇ == i₃₆
                                                                                                                                                                                    && 0 <= i₃₆
                                                                                                                                                                                    && i₃₆ < i₆₀)
                                                                                                                                                                            )
                                                                                                                                                                               ==> a7₅₉[x₃₇] == a7[x₃₇]))
                                                                                                                                                                      && (forall i₃₆: int ::
                                                                                                                                                                            (  i₃₆ <= i₃₆
                                                                                                                                                                              && 0 <= i₃₆
                                                                                                                                                                              && i₃₆ < i₆₀
                                                                                                                                                                               ==> i₃₆ < 100000))
                                                                                                                                                                       ==> (i₆₀ < 100000
                                                                                                                                                                           ==> true
                                                                                                                                                                            && 0 <= i₆₀ + 1
                                                                                                                                                                            && i₆₀ + 1 <= 100000
                                                                                                                                                                            && (forall x₃₇: int ::
                                                                                                                                                                                  ((exists i₃₆: int ::
                                                                                                                                                                                          x₃₇ == i₃₆
                                                                                                                                                                                          && 0 <= i₃₆
                                                                                                                                                                                          && i₃₆ < i₆₀ + 1)
                                                                                                                                                                                     ==> (exists i₃₆: int ::
                                                                                                                                                                                            i₃₆ < 100000
                                                                                                                                                                                            && x₃₇ == i₃₆
                                                                                                                                                                                            && 0 <= i₃₆
                                                                                                                                                                                            && i₃₆ < i₆₀ + 1
                                                                                                                                                                                            && a7₅₉[i₆₀ := a6₅₇[i₆₀]][x₃₇] == a6₅₇[i₃₆])))
                                                                                                                                                                            && (forall x₃₇: int ::
                                                                                                                                                                                  (!((exists i₃₆: int ::
                                                                                                                                                                                          x₃₇ == i₃₆
                                                                                                                                                                                          && 0 <= i₃₆
                                                                                                                                                                                          && i₃₆ < i₆₀ + 1)
                                                                                                                                                                                  )
                                                                                                                                                                                     ==> a7₅₉[i₆₀ := a6₅₇[i₆₀]][x₃₇] == a7[x₃₇]))
                                                                                                                                                                            && (forall i₃₆: int ::
                                                                                                                                                                                  (  i₃₆ <= i₃₆
                                                                                                                                                                                    && 0 <= i₃₆
                                                                                                                                                                                    && i₃₆ < i₆₀ + 1
                                                                                                                                                                                     ==> i₃₆ < 100000))
                                                                                                                                                                            && true
                                                                                                                                                                            && (true
                                                                                                                                                                               ==> true))
                                                                                                                                                                        && (!(i₆₀ < 100000
                                                                                                                                                                        )
                                                                                                                                                                           ==> true
                                                                                                                                                                            && (true
                                                                                                                                                                               ==> true
                                                                                                                                                                                && 0 <= 0
                                                                                                                                                                                && 0 <= 100000
                                                                                                                                                                                && (forall x₄₁: int ::
                                                                                                                                                                                      ((exists i₄₀: int ::
                                                                                                                                                                                              x₄₁ == i₄₀
                                                                                                                                                                                              && 0 <= i₄₀
                                                                                                                                                                                              && i₄₀ < 0)
                                                                                                                                                                                         ==> (exists i₄₀: int ::
                                                                                                                                                                                                i₄₀ < 100000
                                                                                                                                                                                                && x₄₁ == i₄₀
                                                                                                                                                                                                && 0 <= i₄₀
                                                                                                                                                                                                && i₄₀ < 0
                                                                                                                                                                                                && a8[x₄₁] == a7₅₉[i₄₀])))
                                                                                                                                                                                && (forall x₄₁: int ::
                                                                                                                                                                                      (!((exists i₄₀: int ::
                                                                                                                                                                                              x₄₁ == i₄₀
                                                                                                                                                                                              && 0 <= i₄₀
                                                                                                                                                                                              && i₄₀ < 0)
                                                                                                                                                                                      )
                                                                                                                                                                                         ==> a8[x₄₁] == a8[x₄₁]))
                                                                                                                                                                                && (forall i₄₀: int ::
                                                                                                                                                                                      (  i₄₀ <= i₄₀
                                                                                                                                                                                        && 0 <= i₄₀
                                                                                                                                                                                        && i₄₀ < 0
                                                                                                                                                                                         ==> i₄₀ < 100000))
                                                                                                                                                                                && (forall a8₆₁: [int]int, i₆₂: int ::
                                                                                                                                                                                      (  true
                                                                                                                                                                                        && 0 <= i₆₂
                                                                                                                                                                                        && i₆₂ <= 100000
                                                                                                                                                                                        && (forall x₄₁: int ::
                                                                                                                                                                                              ((exists i₄₀: int ::
                                                                                                                                                                                                      x₄₁ == i₄₀
                                                                                                                                                                                                      && 0 <= i₄₀
                                                                                                                                                                                                      && i₄₀ < i₆₂)
                                                                                                                                                                                                 ==> (exists i₄₀: int ::
                                                                                                                                                                                                        i₄₀ < 100000
                                                                                                                                                                                                        && x₄₁ == i₄₀
                                                                                                                                                                                                        && 0 <= i₄₀
                                                                                                                                                                                                        && i₄₀ < i₆₂
                                                                                                                                                                                                        && a8₆₁[x₄₁] == a7₅₉[i₄₀])))
                                                                                                                                                                                        && (forall x₄₁: int ::
                                                                                                                                                                                              (!((exists i₄₀: int ::
                                                                                                                                                                                                      x₄₁ == i₄₀
                                                                                                                                                                                                      && 0 <= i₄₀
                                                                                                                                                                                                      && i₄₀ < i₆₂)
                                                                                                                                                                                              )
                                                                                                                                                                                                 ==> a8₆₁[x₄₁] == a8[x₄₁]))
                                                                                                                                                                                        && (forall i₄₀: int ::
                                                                                                                                                                                              (  i₄₀ <= i₄₀
                                                                                                                                                                                                && 0 <= i₄₀
                                                                                                                                                                                                && i₄₀ < i₆₂
                                                                                                                                                                                                 ==> i₄₀ < 100000))
                                                                                                                                                                                         ==> (i₆₂ < 100000
                                                                                                                                                                                             ==> true
                                                                                                                                                                                              && 0 <= i₆₂ + 1
                                                                                                                                                                                              && i₆₂ + 1 <= 100000
                                                                                                                                                                                              && (forall x₄₁: int ::
                                                                                                                                                                                                    ((exists i₄₀: int ::
                                                                                                                                                                                                            x₄₁ == i₄₀
                                                                                                                                                                                                            && 0 <= i₄₀
                                                                                                                                                                                                            && i₄₀ < i₆₂ + 1)
                                                                                                                                                                                                       ==> (exists i₄₀: int ::
                                                                                                                                                                                                              i₄₀ < 100000
                                                                                                                                                                                                              && x₄₁ == i₄₀
                                                                                                                                                                                                              && 0 <= i₄₀
                                                                                                                                                                                                              && i₄₀ < i₆₂ + 1
                                                                                                                                                                                                              && a8₆₁[i₆₂ := a7₅₉[i₆₂]][x₄₁] == a7₅₉[i₄₀])))
                                                                                                                                                                                              && (forall x₄₁: int ::
                                                                                                                                                                                                    (!((exists i₄₀: int ::
                                                                                                                                                                                                            x₄₁ == i₄₀
                                                                                                                                                                                                            && 0 <= i₄₀
                                                                                                                                                                                                            && i₄₀ < i₆₂ + 1)
                                                                                                                                                                                                    )
                                                                                                                                                                                                       ==> a8₆₁[i₆₂ := a7₅₉[i₆₂]][x₄₁] == a8[x₄₁]))
                                                                                                                                                                                              && (forall i₄₀: int ::
                                                                                                                                                                                                    (  i₄₀ <= i₄₀
                                                                                                                                                                                                      && 0 <= i₄₀
                                                                                                                                                                                                      && i₄₀ < i₆₂ + 1
                                                                                                                                                                                                       ==> i₄₀ < 100000))
                                                                                                                                                                                              && true
                                                                                                                                                                                              && (true
                                                                                                                                                                                                 ==> true))
                                                                                                                                                                                          && (!(i₆₂ < 100000
                                                                                                                                                                                          )
                                                                                                                                                                                             ==> true
                                                                                                                                                                                              && (true
                                                                                                                                                                                                 ==> true
                                                                                                                                                                                                  && 0 <= 0
                                                                                                                                                                                                  && 0 <= 100000
                                                                                                                                                                                                  && (forall x₄₅: int ::
                                                                                                                                                                                                        (  x₄₅ <= x₄₅
                                                                                                                                                                                                          && 0 <= x₄₅
                                                                                                                                                                                                          && x₄₅ < 0
                                                                                                                                                                                                           ==> x₄₅ < 100000))
                                                                                                                                                                                                  && (forall x₆₃: int ::
                                                                                                                                                                                                        (  true
                                                                                                                                                                                                          && 0 <= x₆₃
                                                                                                                                                                                                          && x₆₃ <= 100000
                                                                                                                                                                                                          && (forall x₄₅: int ::
                                                                                                                                                                                                                (  x₄₅ <= x₄₅
                                                                                                                                                                                                                  && 0 <= x₄₅
                                                                                                                                                                                                                  && x₄₅ < x₆₃
                                                                                                                                                                                                                   ==> x₄₅ < 100000))
                                                                                                                                                                                                           ==> (x₆₃ < 100000
                                                                                                                                                                                                               ==> a1₄₇[x₆₃] == a8₆₁[x₆₃]
                                                                                                                                                                                                                && (true
                                                                                                                                                                                                                   ==> true
                                                                                                                                                                                                                    && 0 <= x₆₃ + 1
                                                                                                                                                                                                                    && x₆₃ + 1 <= 100000
                                                                                                                                                                                                                    && (forall x₄₅: int ::
                                                                                                                                                                                                                          (  x₄₅ <= x₄₅
                                                                                                                                                                                                                            && 0 <= x₄₅
                                                                                                                                                                                                                            && x₄₅ < x₆₃ + 1
                                                                                                                                                                                                                             ==> x₄₅ < 100000))
                                                                                                                                                                                                                    && true
                                                                                                                                                                                                                    && (true
                                                                                                                                                                                                                       ==> true)))
                                                                                                                                                                                                            && (!(x₆₃ < 100000
                                                                                                                                                                                                            )
                                                                                                                                                                                                               ==> true
                                                                                                                                                                                                                && (true
                                                                                                                                                                                                                   ==> true))))))))))))))))))))))))))))))))))))))))))));


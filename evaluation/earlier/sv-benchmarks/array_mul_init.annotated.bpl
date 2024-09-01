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
              && (forall x₆: int ::
                    ((exists i₅: int ::
                            x₆ == i₅
                            && 0 <= i₅
                            && i₅ < 0)
                       ==> (exists i₅: int ::
                              i₅ < 100000
                              && x₆ == i₅
                              && 0 <= i₅
                              && i₅ < 0
                              && a[x₆] == i₅)))
              && (forall x₆: int ::
                    (!((exists i₅: int ::
                            x₆ == i₅
                            && 0 <= i₅
                            && i₅ < 0)
                    )
                       ==> a[x₆] == a[x₆]))
              && (forall x₇: int ::
                    ((exists i₅: int ::
                            x₇ == i₅
                            && 0 <= i₅
                            && i₅ < 0)
                       ==> (exists i₅: int ::
                              i₅ < 100000
                              && x₇ == i₅
                              && 0 <= i₅
                              && i₅ < 0
                              && b[x₇] == i₅)))
              && (forall x₇: int ::
                    (!((exists i₅: int ::
                            x₇ == i₅
                            && 0 <= i₅
                            && i₅ < 0)
                    )
                       ==> b[x₇] == b[x₇]))
              && (forall i₅: int ::
                    (  i₅ <= i₅
                      && 0 <= i₅
                      && i₅ < 0
                       ==> i₅ < 100000))
              && (forall a₂₃: [int]int, b₂₄: [int]int, i₂₅: int ::
                    (  true
                      && 0 <= i₂₅
                      && i₂₅ <= 100000
                      && (forall x₆: int ::
                            ((exists i₅: int ::
                                    x₆ == i₅
                                    && 0 <= i₅
                                    && i₅ < i₂₅)
                               ==> (exists i₅: int ::
                                      i₅ < 100000
                                      && x₆ == i₅
                                      && 0 <= i₅
                                      && i₅ < i₂₅
                                      && a₂₃[x₆] == i₅)))
                      && (forall x₆: int ::
                            (!((exists i₅: int ::
                                    x₆ == i₅
                                    && 0 <= i₅
                                    && i₅ < i₂₅)
                            )
                               ==> a₂₃[x₆] == a[x₆]))
                      && (forall x₇: int ::
                            ((exists i₅: int ::
                                    x₇ == i₅
                                    && 0 <= i₅
                                    && i₅ < i₂₅)
                               ==> (exists i₅: int ::
                                      i₅ < 100000
                                      && x₇ == i₅
                                      && 0 <= i₅
                                      && i₅ < i₂₅
                                      && b₂₄[x₇] == i₅)))
                      && (forall x₇: int ::
                            (!((exists i₅: int ::
                                    x₇ == i₅
                                    && 0 <= i₅
                                    && i₅ < i₂₅)
                            )
                               ==> b₂₄[x₇] == b[x₇]))
                      && (forall i₅: int ::
                            (  i₅ <= i₅
                              && 0 <= i₅
                              && i₅ < i₂₅
                               ==> i₅ < 100000))
                       ==> (i₂₅ < 100000
                           ==> true
                            && 0 <= i₂₅ + 1
                            && i₂₅ + 1 <= 100000
                            && (forall x₆: int ::
                                  ((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₅ + 1)
                                     ==> (exists i₅: int ::
                                            i₅ < 100000
                                            && x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₂₅ + 1
                                            && a₂₃[i₂₅ := i₂₅][x₆] == i₅)))
                            && (forall x₆: int ::
                                  (!((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₅ + 1)
                                  )
                                     ==> a₂₃[i₂₅ := i₂₅][x₆] == a[x₆]))
                            && (forall x₇: int ::
                                  ((exists i₅: int ::
                                          x₇ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₅ + 1)
                                     ==> (exists i₅: int ::
                                            i₅ < 100000
                                            && x₇ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₂₅ + 1
                                            && b₂₄[i₂₅ := i₂₅][x₇] == i₅)))
                            && (forall x₇: int ::
                                  (!((exists i₅: int ::
                                          x₇ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₅ + 1)
                                  )
                                     ==> b₂₄[i₂₅ := i₂₅][x₇] == b[x₇]))
                            && (forall i₅: int ::
                                  (  i₅ <= i₅
                                    && 0 <= i₅
                                    && i₅ < i₂₅ + 1
                                     ==> i₅ < 100000))
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
                                && (forall x₁₅: int ::
                                      ((exists i₁₄: int ::
                                              x₁₅ == i₁₄
                                              && 0 <= i₁₄
                                              && i₁₄ < 0)
                                         ==> (exists __VERIFIER_nondet_short₂₁₁: int, k₁₂: int, i₁₄: int ::
                                                __VERIFIER_nondet_short₂₁₁ != 0
                                                && i₁₄ < 100000
                                                && x₁₅ == i₁₄
                                                && 0 <= i₁₄
                                                && i₁₄ < 0
                                                && a₂₃[x₁₅] == k₁₂)))
                                && (forall x₁₅: int ::
                                      (!((exists i₁₄: int ::
                                              x₁₅ == i₁₄
                                              && 0 <= i₁₄
                                              && i₁₄ < 0)
                                      )
                                         ==> a₂₃[x₁₅] == a₂₃[x₁₅]))
                                && (forall x₁₆: int ::
                                      ((exists i₁₄: int ::
                                              x₁₆ == i₁₄
                                              && 0 <= i₁₄
                                              && i₁₄ < 0)
                                         ==> (exists __VERIFIER_nondet_short₂₁₁: int, k₁₂: int, i₁₄: int ::
                                                __VERIFIER_nondet_short₂₁₁ != 0
                                                && i₁₄ < 100000
                                                && x₁₆ == i₁₄
                                                && 0 <= i₁₄
                                                && i₁₄ < 0
                                                && b₂₄[x₁₆] == k₁₂ * k₁₂)))
                                && (forall x₁₆: int ::
                                      (!((exists i₁₄: int ::
                                              x₁₆ == i₁₄
                                              && 0 <= i₁₄
                                              && i₁₄ < 0)
                                      )
                                         ==> b₂₄[x₁₆] == b₂₄[x₁₆]))
                                && (forall i₁₄: int ::
                                      (  i₁₄ <= i₁₄
                                        && 0 <= i₁₄
                                        && i₁₄ < 0
                                         ==> i₁₄ < 100000))
                                && (forall a₂₇: [int]int, b₂₈: [int]int, i₂₉: int ::
                                      (  true
                                        && 0 <= i₂₉
                                        && i₂₉ <= 100000
                                        && (forall x₁₅: int ::
                                              ((exists i₁₄: int ::
                                                      x₁₅ == i₁₄
                                                      && 0 <= i₁₄
                                                      && i₁₄ < i₂₉)
                                                 ==> (exists __VERIFIER_nondet_short₂₁₁: int, k₁₂: int, i₁₄: int ::
                                                        __VERIFIER_nondet_short₂₁₁ != 0
                                                        && i₁₄ < 100000
                                                        && x₁₅ == i₁₄
                                                        && 0 <= i₁₄
                                                        && i₁₄ < i₂₉
                                                        && a₂₇[x₁₅] == k₁₂)))
                                        && (forall x₁₅: int ::
                                              (!((exists i₁₄: int ::
                                                      x₁₅ == i₁₄
                                                      && 0 <= i₁₄
                                                      && i₁₄ < i₂₉)
                                              )
                                                 ==> a₂₇[x₁₅] == a₂₃[x₁₅]))
                                        && (forall x₁₆: int ::
                                              ((exists i₁₄: int ::
                                                      x₁₆ == i₁₄
                                                      && 0 <= i₁₄
                                                      && i₁₄ < i₂₉)
                                                 ==> (exists __VERIFIER_nondet_short₂₁₁: int, k₁₂: int, i₁₄: int ::
                                                        __VERIFIER_nondet_short₂₁₁ != 0
                                                        && i₁₄ < 100000
                                                        && x₁₆ == i₁₄
                                                        && 0 <= i₁₄
                                                        && i₁₄ < i₂₉
                                                        && b₂₈[x₁₆] == k₁₂ * k₁₂)))
                                        && (forall x₁₆: int ::
                                              (!((exists i₁₄: int ::
                                                      x₁₆ == i₁₄
                                                      && 0 <= i₁₄
                                                      && i₁₄ < i₂₉)
                                              )
                                                 ==> b₂₈[x₁₆] == b₂₄[x₁₆]))
                                        && (forall i₁₄: int ::
                                              (  i₁₄ <= i₁₄
                                                && 0 <= i₁₄
                                                && i₁₄ < i₂₉
                                                 ==> i₁₄ < 100000))
                                         ==> (i₂₉ < 100000
                                             ==> (forall __VERIFIER_nondet_short₂: int ::
                                                    (__VERIFIER_nondet_short₂ != 0
                                                       ==> true
                                                        && (forall k₃₂: int ::
                                                              (true
                                                                 ==> true
                                                                  && 0 <= i₂₉ + 1
                                                                  && i₂₉ + 1 <= 100000
                                                                  && (forall x₁₅: int ::
                                                                        ((exists i₁₄: int ::
                                                                                x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₂₉ + 1)
                                                                           ==> (exists __VERIFIER_nondet_short₂₁₁: int, k₁₂: int, i₁₄: int ::
                                                                                  __VERIFIER_nondet_short₂₁₁ != 0
                                                                                  && i₁₄ < 100000
                                                                                  && x₁₅ == i₁₄
                                                                                  && 0 <= i₁₄
                                                                                  && i₁₄ < i₂₉ + 1
                                                                                  && a₂₇[i₂₉ := k₃₂][x₁₅] == k₁₂)))
                                                                  && (forall x₁₅: int ::
                                                                        (!((exists i₁₄: int ::
                                                                                x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₂₉ + 1)
                                                                        )
                                                                           ==> a₂₇[i₂₉ := k₃₂][x₁₅] == a₂₃[x₁₅]))
                                                                  && (forall x₁₆: int ::
                                                                        ((exists i₁₄: int ::
                                                                                x₁₆ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₂₉ + 1)
                                                                           ==> (exists __VERIFIER_nondet_short₂₁₁: int, k₁₂: int, i₁₄: int ::
                                                                                  __VERIFIER_nondet_short₂₁₁ != 0
                                                                                  && i₁₄ < 100000
                                                                                  && x₁₆ == i₁₄
                                                                                  && 0 <= i₁₄
                                                                                  && i₁₄ < i₂₉ + 1
                                                                                  && b₂₈[i₂₉ := k₃₂ * k₃₂][x₁₆] == k₁₂ * k₁₂)))
                                                                  && (forall x₁₆: int ::
                                                                        (!((exists i₁₄: int ::
                                                                                x₁₆ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₂₉ + 1)
                                                                        )
                                                                           ==> b₂₈[i₂₉ := k₃₂ * k₃₂][x₁₆] == b₂₄[x₁₆]))
                                                                  && (forall i₁₄: int ::
                                                                        (  i₁₄ <= i₁₄
                                                                          && 0 <= i₁₄
                                                                          && i₁₄ < i₂₉ + 1
                                                                           ==> i₁₄ < 100000))
                                                                  && true
                                                                  && (true
                                                                     ==> true))))
                                                    && (!(__VERIFIER_nondet_short₂ != 0
                                                    )
                                                       ==> true
                                                        && 0 <= i₂₉ + 1
                                                        && i₂₉ + 1 <= 100000
                                                        && (forall x₁₅: int ::
                                                              ((exists i₁₄: int ::
                                                                      x₁₅ == i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < i₂₉ + 1)
                                                                 ==> (exists __VERIFIER_nondet_short₂₁₁: int, k₁₂: int, i₁₄: int ::
                                                                        __VERIFIER_nondet_short₂₁₁ != 0
                                                                        && i₁₄ < 100000
                                                                        && x₁₅ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₂₉ + 1
                                                                        && a₂₇[x₁₅] == k₁₂)))
                                                        && (forall x₁₅: int ::
                                                              (!((exists i₁₄: int ::
                                                                      x₁₅ == i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < i₂₉ + 1)
                                                              )
                                                                 ==> a₂₇[x₁₅] == a₂₃[x₁₅]))
                                                        && (forall x₁₆: int ::
                                                              ((exists i₁₄: int ::
                                                                      x₁₆ == i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < i₂₉ + 1)
                                                                 ==> (exists __VERIFIER_nondet_short₂₁₁: int, k₁₂: int, i₁₄: int ::
                                                                        __VERIFIER_nondet_short₂₁₁ != 0
                                                                        && i₁₄ < 100000
                                                                        && x₁₆ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₂₉ + 1
                                                                        && b₂₈[x₁₆] == k₁₂ * k₁₂)))
                                                        && (forall x₁₆: int ::
                                                              (!((exists i₁₄: int ::
                                                                      x₁₆ == i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < i₂₉ + 1)
                                                              )
                                                                 ==> b₂₈[x₁₆] == b₂₄[x₁₆]))
                                                        && (forall i₁₄: int ::
                                                              (  i₁₄ <= i₁₄
                                                                && 0 <= i₁₄
                                                                && i₁₄ < i₂₉ + 1
                                                                 ==> i₁₄ < 100000))
                                                        && true
                                                        && (true
                                                           ==> true))))
                                          && (!(i₂₉ < 100000
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= 100000
                                                  && (forall i₂₁: int ::
                                                        (  i₂₁ <= i₂₁
                                                          && 0 <= i₂₁
                                                          && i₂₁ < 0
                                                           ==> i₂₁ < 100000))
                                                  && (forall i₃₀: int ::
                                                        (  true
                                                          && 0 <= i₃₀
                                                          && i₃₀ <= 100000
                                                          && (forall i₂₁: int ::
                                                                (  i₂₁ <= i₂₁
                                                                  && 0 <= i₂₁
                                                                  && i₂₁ < i₃₀
                                                                   ==> i₂₁ < 100000))
                                                           ==> (i₃₀ < 100000
                                                               ==> a₂₇[i₃₀] == b₂₈[i₃₀]
                                                                  || b₂₈[i₃₀] == a₂₇[i₃₀] * a₂₇[i₃₀]
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= i₃₀ + 1
                                                                    && i₃₀ + 1 <= 100000
                                                                    && (forall i₂₁: int ::
                                                                          (  i₂₁ <= i₂₁
                                                                            && 0 <= i₂₁
                                                                            && i₂₁ < i₃₀ + 1
                                                                             ==> i₂₁ < 100000))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(i₃₀ < 100000
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true))))))))))))));


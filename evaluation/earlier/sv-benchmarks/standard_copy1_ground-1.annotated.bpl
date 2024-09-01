data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int ::
      (forall a2: [int]int ::
              true
              && 0 <= 0
              && 0 <= 100000
              && (forall x₆: int ::
                    ((exists a₅: int ::
                            x₆ == a₅
                            && 0 <= a₅
                            && a₅ < 0)
                       ==> (exists __VERIFIER_nondet_int₁₄: int, a₅: int ::
                              a₅ < 100000
                              && x₆ == a₅
                              && 0 <= a₅
                              && a₅ < 0
                              && a1[x₆] == __VERIFIER_nondet_int₁₄)))
              && (forall x₆: int ::
                    (!((exists a₅: int ::
                            x₆ == a₅
                            && 0 <= a₅
                            && a₅ < 0)
                    )
                       ==> a1[x₆] == a1[x₆]))
              && (forall a₅: int ::
                    (  a₅ <= a₅
                      && 0 <= a₅
                      && a₅ < 0
                       ==> a₅ < 100000))
              && (forall a1₁₇: [int]int, a₁₈: int ::
                    (  true
                      && 0 <= a₁₈
                      && a₁₈ <= 100000
                      && (forall x₆: int ::
                            ((exists a₅: int ::
                                    x₆ == a₅
                                    && 0 <= a₅
                                    && a₅ < a₁₈)
                               ==> (exists __VERIFIER_nondet_int₁₄: int, a₅: int ::
                                      a₅ < 100000
                                      && x₆ == a₅
                                      && 0 <= a₅
                                      && a₅ < a₁₈
                                      && a1₁₇[x₆] == __VERIFIER_nondet_int₁₄)))
                      && (forall x₆: int ::
                            (!((exists a₅: int ::
                                    x₆ == a₅
                                    && 0 <= a₅
                                    && a₅ < a₁₈)
                            )
                               ==> a1₁₇[x₆] == a1[x₆]))
                      && (forall a₅: int ::
                            (  a₅ <= a₅
                              && 0 <= a₅
                              && a₅ < a₁₈
                               ==> a₅ < 100000))
                       ==> (a₁₈ < 100000
                           ==> (forall __VERIFIER_nondet_int₁: int ::
                                  true
                                  && 0 <= a₁₈ + 1
                                  && a₁₈ + 1 <= 100000
                                  && (forall x₆: int ::
                                        ((exists a₅: int ::
                                                x₆ == a₅
                                                && 0 <= a₅
                                                && a₅ < a₁₈ + 1)
                                           ==> (exists __VERIFIER_nondet_int₁₄: int, a₅: int ::
                                                  a₅ < 100000
                                                  && x₆ == a₅
                                                  && 0 <= a₅
                                                  && a₅ < a₁₈ + 1
                                                  && a1₁₇[a₁₈ := __VERIFIER_nondet_int₁][x₆] == __VERIFIER_nondet_int₁₄)))
                                  && (forall x₆: int ::
                                        (!((exists a₅: int ::
                                                x₆ == a₅
                                                && 0 <= a₅
                                                && a₅ < a₁₈ + 1)
                                        )
                                           ==> a1₁₇[a₁₈ := __VERIFIER_nondet_int₁][x₆] == a1[x₆]))
                                  && (forall a₅: int ::
                                        (  a₅ <= a₅
                                          && 0 <= a₅
                                          && a₅ < a₁₈ + 1
                                           ==> a₅ < 100000))
                                  && true
                                  && (true
                                     ==> true)))
                        && (!(a₁₈ < 100000
                        )
                           ==> true
                            && (true
                               ==> true
                                && 0 <= 0
                                && 0 <= 100000
                                && (forall x₁₁: int ::
                                      ((exists i₁₀: int ::
                                              x₁₁ == i₁₀
                                              && 0 <= i₁₀
                                              && i₁₀ < 0)
                                         ==> (exists i₁₀: int ::
                                                i₁₀ < 100000
                                                && x₁₁ == i₁₀
                                                && 0 <= i₁₀
                                                && i₁₀ < 0
                                                && a2[x₁₁] == a1₁₇[i₁₀])))
                                && (forall x₁₁: int ::
                                      (!((exists i₁₀: int ::
                                              x₁₁ == i₁₀
                                              && 0 <= i₁₀
                                              && i₁₀ < 0)
                                      )
                                         ==> a2[x₁₁] == a2[x₁₁]))
                                && (forall i₁₀: int ::
                                      (  i₁₀ <= i₁₀
                                        && 0 <= i₁₀
                                        && i₁₀ < 0
                                         ==> i₁₀ < 100000))
                                && (forall a2₁₉: [int]int, i₂₀: int ::
                                      (  true
                                        && 0 <= i₂₀
                                        && i₂₀ <= 100000
                                        && (forall x₁₁: int ::
                                              ((exists i₁₀: int ::
                                                      x₁₁ == i₁₀
                                                      && 0 <= i₁₀
                                                      && i₁₀ < i₂₀)
                                                 ==> (exists i₁₀: int ::
                                                        i₁₀ < 100000
                                                        && x₁₁ == i₁₀
                                                        && 0 <= i₁₀
                                                        && i₁₀ < i₂₀
                                                        && a2₁₉[x₁₁] == a1₁₇[i₁₀])))
                                        && (forall x₁₁: int ::
                                              (!((exists i₁₀: int ::
                                                      x₁₁ == i₁₀
                                                      && 0 <= i₁₀
                                                      && i₁₀ < i₂₀)
                                              )
                                                 ==> a2₁₉[x₁₁] == a2[x₁₁]))
                                        && (forall i₁₀: int ::
                                              (  i₁₀ <= i₁₀
                                                && 0 <= i₁₀
                                                && i₁₀ < i₂₀
                                                 ==> i₁₀ < 100000))
                                         ==> (i₂₀ < 100000
                                             ==> true
                                              && 0 <= i₂₀ + 1
                                              && i₂₀ + 1 <= 100000
                                              && (forall x₁₁: int ::
                                                    ((exists i₁₀: int ::
                                                            x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₂₀ + 1)
                                                       ==> (exists i₁₀: int ::
                                                              i₁₀ < 100000
                                                              && x₁₁ == i₁₀
                                                              && 0 <= i₁₀
                                                              && i₁₀ < i₂₀ + 1
                                                              && a2₁₉[i₂₀ := a1₁₇[i₂₀]][x₁₁] == a1₁₇[i₁₀])))
                                              && (forall x₁₁: int ::
                                                    (!((exists i₁₀: int ::
                                                            x₁₁ == i₁₀
                                                            && 0 <= i₁₀
                                                            && i₁₀ < i₂₀ + 1)
                                                    )
                                                       ==> a2₁₉[i₂₀ := a1₁₇[i₂₀]][x₁₁] == a2[x₁₁]))
                                              && (forall i₁₀: int ::
                                                    (  i₁₀ <= i₁₀
                                                      && 0 <= i₁₀
                                                      && i₁₀ < i₂₀ + 1
                                                       ==> i₁₀ < 100000))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (!(i₂₀ < 100000
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₁₅: int ::
                                                        (  x₁₅ <= x₁₅
                                                          && 0 <= x₁₅
                                                          && x₁₅ < 0
                                                           ==> x₁₅ < 100000))
                                                  && (forall x₂₁: int ::
                                                        (  true
                                                          && 0 <= x₂₁
                                                          && x₂₁ <= 100000
                                                          && (forall x₁₅: int ::
                                                                (  x₁₅ <= x₁₅
                                                                  && 0 <= x₁₅
                                                                  && x₁₅ < x₂₁
                                                                   ==> x₁₅ < 100000))
                                                           ==> (x₂₁ < 100000
                                                               ==> a1₁₇[x₂₁] == a2₁₉[x₂₁]
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= x₂₁ + 1
                                                                    && x₂₁ + 1 <= 100000
                                                                    && (forall x₁₅: int ::
                                                                          (  x₁₅ <= x₁₅
                                                                            && 0 <= x₁₅
                                                                            && x₁₅ < x₂₁ + 1
                                                                             ==> x₁₅ < 100000))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(x₂₁ < 100000
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true))))))))))))));


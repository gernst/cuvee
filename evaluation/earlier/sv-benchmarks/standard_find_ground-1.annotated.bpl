data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
      (forall __VERIFIER_nondet_int₁: int ::
              true
              && 0 <= 0
              && 0 <= 100000
              && (forall x₇: int ::
                    ((exists j₆: int ::
                            x₇ == j₆
                            && 0 <= j₆
                            && j₆ < 0)
                       ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                              j₆ < 100000
                              && x₇ == j₆
                              && 0 <= j₆
                              && j₆ < 0
                              && a[x₇] == __VERIFIER_nondet_int₂₅)))
              && (forall x₇: int ::
                    (!((exists j₆: int ::
                            x₇ == j₆
                            && 0 <= j₆
                            && j₆ < 0)
                    )
                       ==> a[x₇] == a[x₇]))
              && (forall j₆: int ::
                    (  j₆ <= j₆
                      && 0 <= j₆
                      && j₆ < 0
                       ==> j₆ < 100000))
              && (forall a₁₅: [int]int, j₁₆: int ::
                    (  true
                      && 0 <= j₁₆
                      && j₁₆ <= 100000
                      && (forall x₇: int ::
                            ((exists j₆: int ::
                                    x₇ == j₆
                                    && 0 <= j₆
                                    && j₆ < j₁₆)
                               ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                                      j₆ < 100000
                                      && x₇ == j₆
                                      && 0 <= j₆
                                      && j₆ < j₁₆
                                      && a₁₅[x₇] == __VERIFIER_nondet_int₂₅)))
                      && (forall x₇: int ::
                            (!((exists j₆: int ::
                                    x₇ == j₆
                                    && 0 <= j₆
                                    && j₆ < j₁₆)
                            )
                               ==> a₁₅[x₇] == a[x₇]))
                      && (forall j₆: int ::
                            (  j₆ <= j₆
                              && 0 <= j₆
                              && j₆ < j₁₆
                               ==> j₆ < 100000))
                       ==> (j₁₆ < 100000
                           ==> (forall __VERIFIER_nondet_int₂: int ::
                                  true
                                  && 0 <= j₁₆ + 1
                                  && j₁₆ + 1 <= 100000
                                  && (forall x₇: int ::
                                        ((exists j₆: int ::
                                                x₇ == j₆
                                                && 0 <= j₆
                                                && j₆ < j₁₆ + 1)
                                           ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                                                  j₆ < 100000
                                                  && x₇ == j₆
                                                  && 0 <= j₆
                                                  && j₆ < j₁₆ + 1
                                                  && a₁₅[j₁₆ := __VERIFIER_nondet_int₂][x₇] == __VERIFIER_nondet_int₂₅)))
                                  && (forall x₇: int ::
                                        (!((exists j₆: int ::
                                                x₇ == j₆
                                                && 0 <= j₆
                                                && j₆ < j₁₆ + 1)
                                        )
                                           ==> a₁₅[j₁₆ := __VERIFIER_nondet_int₂][x₇] == a[x₇]))
                                  && (forall j₆: int ::
                                        (  j₆ <= j₆
                                          && 0 <= j₆
                                          && j₆ < j₁₆ + 1
                                           ==> j₆ < 100000))
                                  && true
                                  && (true
                                     ==> true)))
                        && (!(j₁₆ < 100000
                        )
                           ==> true
                            && (true
                               ==> true
                                && 0 <= 0
                                && 0 <= 100000
                                && (forall i₁₀: int ::
                                      (  i₁₀ <= i₁₀
                                        && 0 <= i₁₀
                                        && i₁₀ < 0
                                         ==> i₁₀ < 100000
                                          && a₁₅[i₁₀] != __VERIFIER_nondet_int₁))
                                && (forall i₁₇: int ::
                                      (  true
                                        && 0 <= i₁₇
                                        && i₁₇ <= 100000
                                        && (forall i₁₀: int ::
                                              (  i₁₀ <= i₁₀
                                                && 0 <= i₁₀
                                                && i₁₀ < i₁₇
                                                 ==> i₁₀ < 100000
                                                  && a₁₅[i₁₀] != __VERIFIER_nondet_int₁))
                                         ==> (  i₁₇ < 100000
                                            && a₁₅[i₁₇] != __VERIFIER_nondet_int₁
                                             ==> true
                                              && 0 <= i₁₇ + 1
                                              && i₁₇ + 1 <= 100000
                                              && (forall i₁₀: int ::
                                                    (  i₁₀ <= i₁₀
                                                      && 0 <= i₁₀
                                                      && i₁₀ < i₁₇ + 1
                                                       ==> i₁₀ < 100000
                                                        && a₁₅[i₁₀] != __VERIFIER_nondet_int₁))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (!(  i₁₇ < 100000
                                            && a₁₅[i₁₇] != __VERIFIER_nondet_int₁
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= i₁₇
                                                  && (forall x₁₃: int ::
                                                        (  x₁₃ <= x₁₃
                                                          && 0 <= x₁₃
                                                          && x₁₃ < 0
                                                           ==> x₁₃ < i₁₇))
                                                  && (forall x₁₈: int ::
                                                        (  true
                                                          && 0 <= x₁₈
                                                          && x₁₈ <= i₁₇
                                                          && (forall x₁₃: int ::
                                                                (  x₁₃ <= x₁₃
                                                                  && 0 <= x₁₃
                                                                  && x₁₃ < x₁₈
                                                                   ==> x₁₃ < i₁₇))
                                                           ==> (x₁₈ < i₁₇
                                                               ==> a₁₅[x₁₈] != __VERIFIER_nondet_int₁
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= x₁₈ + 1
                                                                    && x₁₈ + 1 <= i₁₇
                                                                    && (forall x₁₃: int ::
                                                                          (  x₁₃ <= x₁₃
                                                                            && 0 <= x₁₃
                                                                            && x₁₃ < x₁₈ + 1
                                                                             ==> x₁₃ < i₁₇))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(x₁₈ < i₁₇
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall A: [int]int ::
      (forall B: [int]int ::
            (forall C: [int]int ::
                    true
                    && 0 <= 0
                    && 0 <= 100000
                    && (forall x₈: int ::
                          ((exists i₇: int ::
                                  x₈ == i₇
                                  && 0 <= i₇
                                  && i₇ < 0)
                             ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                    i₇ < 100000
                                    && x₈ == i₇
                                    && 0 <= i₇
                                    && i₇ < 0
                                    && A[x₈] == __VERIFIER_nondet_int₁₅)))
                    && (forall x₈: int ::
                          (!((exists i₇: int ::
                                  x₈ == i₇
                                  && 0 <= i₇
                                  && i₇ < 0)
                          )
                             ==> A[x₈] == A[x₈]))
                    && (forall x₉: int ::
                          ((exists i₇: int ::
                                  x₉ == i₇
                                  && 0 <= i₇
                                  && i₇ < 0)
                             ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                                    i₇ < 100000
                                    && x₉ == i₇
                                    && 0 <= i₇
                                    && i₇ < 0
                                    && B[x₉] == __VERIFIER_nondet_int₂₆)))
                    && (forall x₉: int ::
                          (!((exists i₇: int ::
                                  x₉ == i₇
                                  && 0 <= i₇
                                  && i₇ < 0)
                          )
                             ==> B[x₉] == B[x₉]))
                    && (forall i₇: int ::
                          (  i₇ <= i₇
                            && 0 <= i₇
                            && i₇ < 0
                             ==> i₇ < 100000))
                    && (forall A₂₄: [int]int, B₂₅: [int]int, i₂₆: int ::
                          (  true
                            && 0 <= i₂₆
                            && i₂₆ <= 100000
                            && (forall x₈: int ::
                                  ((exists i₇: int ::
                                          x₈ == i₇
                                          && 0 <= i₇
                                          && i₇ < i₂₆)
                                     ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                            i₇ < 100000
                                            && x₈ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₂₆
                                            && A₂₄[x₈] == __VERIFIER_nondet_int₁₅)))
                            && (forall x₈: int ::
                                  (!((exists i₇: int ::
                                          x₈ == i₇
                                          && 0 <= i₇
                                          && i₇ < i₂₆)
                                  )
                                     ==> A₂₄[x₈] == A[x₈]))
                            && (forall x₉: int ::
                                  ((exists i₇: int ::
                                          x₉ == i₇
                                          && 0 <= i₇
                                          && i₇ < i₂₆)
                                     ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                                            i₇ < 100000
                                            && x₉ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₂₆
                                            && B₂₅[x₉] == __VERIFIER_nondet_int₂₆)))
                            && (forall x₉: int ::
                                  (!((exists i₇: int ::
                                          x₉ == i₇
                                          && 0 <= i₇
                                          && i₇ < i₂₆)
                                  )
                                     ==> B₂₅[x₉] == B[x₉]))
                            && (forall i₇: int ::
                                  (  i₇ <= i₇
                                    && 0 <= i₇
                                    && i₇ < i₂₆
                                     ==> i₇ < 100000))
                             ==> (i₂₆ < 100000
                                 ==> (forall __VERIFIER_nondet_int₁: int ::
                                      (forall __VERIFIER_nondet_int₂: int ::
                                              true
                                              && 0 <= i₂₆ + 1
                                              && i₂₆ + 1 <= 100000
                                              && (forall x₈: int ::
                                                    ((exists i₇: int ::
                                                            x₈ == i₇
                                                            && 0 <= i₇
                                                            && i₇ < i₂₆ + 1)
                                                       ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                                              i₇ < 100000
                                                              && x₈ == i₇
                                                              && 0 <= i₇
                                                              && i₇ < i₂₆ + 1
                                                              && A₂₄[i₂₆ := __VERIFIER_nondet_int₁][x₈] == __VERIFIER_nondet_int₁₅)))
                                              && (forall x₈: int ::
                                                    (!((exists i₇: int ::
                                                            x₈ == i₇
                                                            && 0 <= i₇
                                                            && i₇ < i₂₆ + 1)
                                                    )
                                                       ==> A₂₄[i₂₆ := __VERIFIER_nondet_int₁][x₈] == A[x₈]))
                                              && (forall x₉: int ::
                                                    ((exists i₇: int ::
                                                            x₉ == i₇
                                                            && 0 <= i₇
                                                            && i₇ < i₂₆ + 1)
                                                       ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                                                              i₇ < 100000
                                                              && x₉ == i₇
                                                              && 0 <= i₇
                                                              && i₇ < i₂₆ + 1
                                                              && B₂₅[i₂₆ := __VERIFIER_nondet_int₂][x₉] == __VERIFIER_nondet_int₂₆)))
                                              && (forall x₉: int ::
                                                    (!((exists i₇: int ::
                                                            x₉ == i₇
                                                            && 0 <= i₇
                                                            && i₇ < i₂₆ + 1)
                                                    )
                                                       ==> B₂₅[i₂₆ := __VERIFIER_nondet_int₂][x₉] == B[x₉]))
                                              && (forall i₇: int ::
                                                    (  i₇ <= i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₂₆ + 1
                                                       ==> i₇ < 100000))
                                              && true
                                              && (true
                                                 ==> true))))
                              && (!(i₂₆ < 100000
                              )
                                 ==> true
                                  && (true
                                     ==> true
                                      && 0 <= 0
                                      && 0 <= 0
                                      && 0 <= 100000
                                      && (forall x₁₅: int ::
                                            ((exists j₁₃: int ::
                                                    x₁₅ == j₁₃
                                                    && 0 <= j₁₃
                                                    && j₁₃ < 0)
                                               ==> (exists j₁₃: int, i₁₄: int ::
                                                      A₂₄[i₁₄] == B₂₅[i₁₄]
                                                      && i₁₄ < 100000
                                                      && x₁₅ == j₁₃
                                                      && 0 <= j₁₃
                                                      && j₁₃ < 0
                                                      && 0 <= i₁₄
                                                      && i₁₄ < 0
                                                      && C[x₁₅] == i₁₄)))
                                      && (forall x₁₅: int ::
                                            (!((exists j₁₃: int ::
                                                    x₁₅ == j₁₃
                                                    && 0 <= j₁₃
                                                    && j₁₃ < 0)
                                            )
                                               ==> C[x₁₅] == C[x₁₅]))
                                      && (forall j₁₃: int, i₁₄: int ::
                                            (  j₁₃ <= j₁₃
                                              && i₁₄ <= i₁₄
                                              && 0 <= j₁₃
                                              && j₁₃ < 0
                                              && 0 <= i₁₄
                                              && i₁₄ < 0
                                               ==> i₁₄ < 100000))
                                      && (forall C₂₇: [int]int, j₂₈: int, i₂₉: int ::
                                            (  true
                                              && 0 <= j₂₈
                                              && 0 <= i₂₉
                                              && i₂₉ <= 100000
                                              && (forall x₁₅: int ::
                                                    ((exists j₁₃: int ::
                                                            x₁₅ == j₁₃
                                                            && 0 <= j₁₃
                                                            && j₁₃ < j₂₈)
                                                       ==> (exists j₁₃: int, i₁₄: int ::
                                                              A₂₄[i₁₄] == B₂₅[i₁₄]
                                                              && i₁₄ < 100000
                                                              && x₁₅ == j₁₃
                                                              && 0 <= j₁₃
                                                              && j₁₃ < j₂₈
                                                              && 0 <= i₁₄
                                                              && i₁₄ < i₂₉
                                                              && C₂₇[x₁₅] == i₁₄)))
                                              && (forall x₁₅: int ::
                                                    (!((exists j₁₃: int ::
                                                            x₁₅ == j₁₃
                                                            && 0 <= j₁₃
                                                            && j₁₃ < j₂₈)
                                                    )
                                                       ==> C₂₇[x₁₅] == C[x₁₅]))
                                              && (forall j₁₃: int, i₁₄: int ::
                                                    (  j₁₃ <= j₁₃
                                                      && i₁₄ <= i₁₄
                                                      && 0 <= j₁₃
                                                      && j₁₃ < j₂₈
                                                      && 0 <= i₁₄
                                                      && i₁₄ < i₂₉
                                                       ==> i₁₄ < 100000))
                                               ==> (i₂₉ < 100000
                                                   ==> (A₂₄[i₂₉] == B₂₅[i₂₉]
                                                       ==> true
                                                        && 0 <= j₂₈ + 1
                                                        && 0 <= i₂₉ + 1
                                                        && i₂₉ + 1 <= 100000
                                                        && (forall x₁₅: int ::
                                                              ((exists j₁₃: int ::
                                                                      x₁₅ == j₁₃
                                                                      && 0 <= j₁₃
                                                                      && j₁₃ < j₂₈ + 1)
                                                                 ==> (exists j₁₃: int, i₁₄: int ::
                                                                        A₂₄[i₁₄] == B₂₅[i₁₄]
                                                                        && i₁₄ < 100000
                                                                        && x₁₅ == j₁₃
                                                                        && 0 <= j₁₃
                                                                        && j₁₃ < j₂₈ + 1
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₂₉ + 1
                                                                        && C₂₇[j₂₈ := i₂₉][x₁₅] == i₁₄)))
                                                        && (forall x₁₅: int ::
                                                              (!((exists j₁₃: int ::
                                                                      x₁₅ == j₁₃
                                                                      && 0 <= j₁₃
                                                                      && j₁₃ < j₂₈ + 1)
                                                              )
                                                                 ==> C₂₇[j₂₈ := i₂₉][x₁₅] == C[x₁₅]))
                                                        && (forall j₁₃: int, i₁₄: int ::
                                                              (  j₁₃ <= j₁₃
                                                                && i₁₄ <= i₁₄
                                                                && 0 <= j₁₃
                                                                && j₁₃ < j₂₈ + 1
                                                                && 0 <= i₁₄
                                                                && i₁₄ < i₂₉ + 1
                                                                 ==> i₁₄ < 100000))
                                                        && true
                                                        && (true
                                                           ==> true))
                                                    && (A₂₄[i₂₉] != B₂₅[i₂₉]
                                                       ==> true
                                                        && 0 <= j₂₈
                                                        && 0 <= i₂₉ + 1
                                                        && i₂₉ + 1 <= 100000
                                                        && (forall x₁₅: int ::
                                                              ((exists j₁₃: int ::
                                                                      x₁₅ == j₁₃
                                                                      && 0 <= j₁₃
                                                                      && j₁₃ < j₂₈)
                                                                 ==> (exists j₁₃: int, i₁₄: int ::
                                                                        A₂₄[i₁₄] == B₂₅[i₁₄]
                                                                        && i₁₄ < 100000
                                                                        && x₁₅ == j₁₃
                                                                        && 0 <= j₁₃
                                                                        && j₁₃ < j₂₈
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₂₉ + 1
                                                                        && C₂₇[x₁₅] == i₁₄)))
                                                        && (forall x₁₅: int ::
                                                              (!((exists j₁₃: int ::
                                                                      x₁₅ == j₁₃
                                                                      && 0 <= j₁₃
                                                                      && j₁₃ < j₂₈)
                                                              )
                                                                 ==> C₂₇[x₁₅] == C[x₁₅]))
                                                        && (forall j₁₃: int, i₁₄: int ::
                                                              (  j₁₃ <= j₁₃
                                                                && i₁₄ <= i₁₄
                                                                && 0 <= j₁₃
                                                                && j₁₃ < j₂₈
                                                                && 0 <= i₁₄
                                                                && i₁₄ < i₂₉ + 1
                                                                 ==> i₁₄ < 100000))
                                                        && true
                                                        && (true
                                                           ==> true)))
                                                && (!(i₂₉ < 100000
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> true
                                                        && 0 <= 0
                                                        && 0 <= j₂₈
                                                        && (forall x₂₀: int ::
                                                              (  x₂₀ <= x₂₀
                                                                && 0 <= x₂₀
                                                                && x₂₀ < 0
                                                                 ==> x₂₀ < j₂₈))
                                                        && (forall x₃₀: int ::
                                                              (  true
                                                                && 0 <= x₃₀
                                                                && x₃₀ <= j₂₈
                                                                && (forall x₂₀: int ::
                                                                      (  x₂₀ <= x₂₀
                                                                        && 0 <= x₂₀
                                                                        && x₂₀ < x₃₀
                                                                         ==> x₂₀ < j₂₈))
                                                                 ==> (x₃₀ < j₂₈
                                                                     ==> C₂₇[x₃₀] <= x₃₀ + i₂₉ - j₂₈
                                                                      && (true
                                                                         ==> true
                                                                          && 0 <= x₃₀ + 1
                                                                          && x₃₀ + 1 <= j₂₈
                                                                          && (forall x₂₀: int ::
                                                                                (  x₂₀ <= x₂₀
                                                                                  && 0 <= x₂₀
                                                                                  && x₂₀ < x₃₀ + 1
                                                                                   ==> x₂₀ < j₂₈))
                                                                          && true
                                                                          && (true
                                                                             ==> true)))
                                                                  && (!(x₃₀ < j₂₈
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true
                                                                          && 0 <= 0
                                                                          && 0 <= j₂₈
                                                                          && (forall x₂₂: int ::
                                                                                (  x₂₂ <= x₂₂
                                                                                  && 0 <= x₂₂
                                                                                  && x₂₂ < 0
                                                                                   ==> x₂₂ < j₂₈))
                                                                          && (forall x₃₁: int ::
                                                                                (  true
                                                                                  && 0 <= x₃₁
                                                                                  && x₃₁ <= j₂₈
                                                                                  && (forall x₂₂: int ::
                                                                                        (  x₂₂ <= x₂₂
                                                                                          && 0 <= x₂₂
                                                                                          && x₂₂ < x₃₁
                                                                                           ==> x₂₂ < j₂₈))
                                                                                   ==> (x₃₁ < j₂₈
                                                                                       ==> x₃₁ <= C₂₇[x₃₁]
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 0 <= x₃₁ + 1
                                                                                            && x₃₁ + 1 <= j₂₈
                                                                                            && (forall x₂₂: int ::
                                                                                                  (  x₂₂ <= x₂₂
                                                                                                    && 0 <= x₂₂
                                                                                                    && x₂₂ < x₃₁ + 1
                                                                                                     ==> x₂₂ < j₂₈))
                                                                                            && true
                                                                                            && (true
                                                                                               ==> true)))
                                                                                    && (!(x₃₁ < j₂₈
                                                                                    )
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true)))))))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall A: [int]int ::
        true
        && 0 <= 0
        && 0 <= 100000
        && (forall x₅: int ::
              ((exists i₄: int ::
                      x₅ == i₄
                      && 0 <= i₄
                      && i₄ < 0)
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 100000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < 0
                        && A[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
              (!((exists i₄: int ::
                      x₅ == i₄
                      && 0 <= i₄
                      && i₄ < 0)
              )
                 ==> A[x₅] == A[x₅]))
        && (forall i₄: int ::
              (  i₄ <= i₄
                && 0 <= i₄
                && i₄ < 0
                 ==> i₄ < 100000))
        && (forall A₁₅: [int]int, i₁₆: int ::
              (  true
                && 0 <= i₁₆
                && i₁₆ <= 100000
                && (forall x₅: int ::
                      ((exists i₄: int ::
                              x₅ == i₄
                              && 0 <= i₄
                              && i₄ < i₁₆)
                         ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                i₄ < 100000
                                && x₅ == i₄
                                && 0 <= i₄
                                && i₄ < i₁₆
                                && A₁₅[x₅] == __VERIFIER_nondet_int₁₃)))
                && (forall x₅: int ::
                      (!((exists i₄: int ::
                              x₅ == i₄
                              && 0 <= i₄
                              && i₄ < i₁₆)
                      )
                         ==> A₁₅[x₅] == A[x₅]))
                && (forall i₄: int ::
                      (  i₄ <= i₄
                        && 0 <= i₄
                        && i₄ < i₁₆
                         ==> i₄ < 100000))
                 ==> (i₁₆ < 100000
                     ==> (forall __VERIFIER_nondet_int₁: int ::
                            true
                            && 0 <= i₁₆ + 1
                            && i₁₆ + 1 <= 100000
                            && (forall x₅: int ::
                                  ((exists i₄: int ::
                                          x₅ == i₄
                                          && 0 <= i₄
                                          && i₄ < i₁₆ + 1)
                                     ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                            i₄ < 100000
                                            && x₅ == i₄
                                            && 0 <= i₄
                                            && i₄ < i₁₆ + 1
                                            && A₁₅[i₁₆ := __VERIFIER_nondet_int₁][x₅] == __VERIFIER_nondet_int₁₃)))
                            && (forall x₅: int ::
                                  (!((exists i₄: int ::
                                          x₅ == i₄
                                          && 0 <= i₄
                                          && i₄ < i₁₆ + 1)
                                  )
                                     ==> A₁₅[i₁₆ := __VERIFIER_nondet_int₁][x₅] == A[x₅]))
                            && (forall i₄: int ::
                                  (  i₄ <= i₄
                                    && 0 <= i₄
                                    && i₄ < i₁₆ + 1
                                     ==> i₄ < 100000))
                            && true
                            && (true
                               ==> true)))
                  && (!(i₁₆ < 100000
                  )
                     ==> true
                      && (true
                         ==> true
                          && 0 <= 0
                          && 0 <= 100000 / 2
                          && (forall x₉: int ::
                                ((exists i₈: int ::
                                        x₉ == i₈
                                        && 0 <= i₈
                                        && i₈ < 0)
                                   ==> (exists i₈: int ::
                                          i₈ < 100000 / 2
                                          && x₉ == i₈
                                          && 0 <= i₈
                                          && i₈ < 0
                                          && A₁₅[x₉] == A₁₅[99999 + -i₈])))
                          && (forall x₉: int ::
                                (!((exists i₈: int ::
                                        x₉ == i₈
                                        && 0 <= i₈
                                        && i₈ < 0)
                                )
                                   ==> A₁₅[x₉] == A₁₅[x₉]))
                          && (forall i₈: int ::
                                (  i₈ <= i₈
                                  && 0 <= i₈
                                  && i₈ < 0
                                   ==> i₈ < 100000 / 2))
                          && (forall A₁₇: [int]int, i₁₈: int ::
                                (  true
                                  && 0 <= i₁₈
                                  && i₁₈ <= 100000 / 2
                                  && (forall x₉: int ::
                                        ((exists i₈: int ::
                                                x₉ == i₈
                                                && 0 <= i₈
                                                && i₈ < i₁₈)
                                           ==> (exists i₈: int ::
                                                  i₈ < 100000 / 2
                                                  && x₉ == i₈
                                                  && 0 <= i₈
                                                  && i₈ < i₁₈
                                                  && A₁₇[x₉] == A₁₅[99999 + -i₈])))
                                  && (forall x₉: int ::
                                        (!((exists i₈: int ::
                                                x₉ == i₈
                                                && 0 <= i₈
                                                && i₈ < i₁₈)
                                        )
                                           ==> A₁₇[x₉] == A₁₅[x₉]))
                                  && (forall i₈: int ::
                                        (  i₈ <= i₈
                                          && 0 <= i₈
                                          && i₈ < i₁₈
                                           ==> i₈ < 100000 / 2))
                                   ==> (i₁₈ < 100000 / 2
                                       ==> true
                                        && 0 <= i₁₈ + 1
                                        && i₁₈ + 1 <= 100000 / 2
                                        && (forall x₉: int ::
                                              ((exists i₈: int ::
                                                      x₉ == i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₈ + 1)
                                                 ==> (exists i₈: int ::
                                                        i₈ < 100000 / 2
                                                        && x₉ == i₈
                                                        && 0 <= i₈
                                                        && i₈ < i₁₈ + 1
                                                        && A₁₇[i₁₈ := A₁₇[100000 - i₁₈ - 1]][x₉] == A₁₅[99999 + -i₈])))
                                        && (forall x₉: int ::
                                              (!((exists i₈: int ::
                                                      x₉ == i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₈ + 1)
                                              )
                                                 ==> A₁₇[i₁₈ := A₁₇[100000 - i₁₈ - 1]][x₉] == A₁₅[x₉]))
                                        && (forall i₈: int ::
                                              (  i₈ <= i₈
                                                && 0 <= i₈
                                                && i₈ < i₁₈ + 1
                                                 ==> i₈ < 100000 / 2))
                                        && true
                                        && (true
                                           ==> true))
                                    && (!(i₁₈ < 100000 / 2
                                    )
                                       ==> true
                                        && (true
                                           ==> true
                                            && 0 <= 0
                                            && 0 <= 100000 / 2
                                            && (forall x₁₃: int ::
                                                  (  x₁₃ <= x₁₃
                                                    && 0 <= x₁₃
                                                    && x₁₃ < 0
                                                     ==> x₁₃ < 100000 / 2))
                                            && (forall x₁₉: int ::
                                                  (  true
                                                    && 0 <= x₁₉
                                                    && x₁₉ <= 100000 / 2
                                                    && (forall x₁₃: int ::
                                                          (  x₁₃ <= x₁₃
                                                            && 0 <= x₁₃
                                                            && x₁₃ < x₁₉
                                                             ==> x₁₃ < 100000 / 2))
                                                     ==> (x₁₉ < 100000 / 2
                                                         ==> A₁₇[x₁₉] == A₁₇[100000 - x₁₉ - 1]
                                                          && (true
                                                             ==> true
                                                              && 0 <= x₁₉ + 1
                                                              && x₁₉ + 1 <= 100000 / 2
                                                              && (forall x₁₃: int ::
                                                                    (  x₁₃ <= x₁₃
                                                                      && 0 <= x₁₃
                                                                      && x₁₃ < x₁₉ + 1
                                                                       ==> x₁₃ < 100000 / 2))
                                                              && true
                                                              && (true
                                                                 ==> true)))
                                                      && (!(x₁₉ < 100000 / 2
                                                      )
                                                         ==> true
                                                          && (true
                                                             ==> true)))))))))))));


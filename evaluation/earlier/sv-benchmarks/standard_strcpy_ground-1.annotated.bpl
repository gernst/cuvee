data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall src: [int]int ::
      (forall dst: [int]int ::
              true
              && 0 <= 0
              && 0 <= 100000
              && (forall x₅: int ::
                    ((exists j₄: int ::
                            x₅ == j₄
                            && 0 <= j₄
                            && j₄ < 0)
                       ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                              j₄ < 100000
                              && x₅ == j₄
                              && 0 <= j₄
                              && j₄ < 0
                              && src[x₅] == __VERIFIER_nondet_int₁₃)))
              && (forall x₅: int ::
                    (!((exists j₄: int ::
                            x₅ == j₄
                            && 0 <= j₄
                            && j₄ < 0)
                    )
                       ==> src[x₅] == src[x₅]))
              && (forall j₄: int ::
                    (  j₄ <= j₄
                      && 0 <= j₄
                      && j₄ < 0
                       ==> j₄ < 100000))
              && (forall src₁₅: [int]int, j₁₆: int ::
                    (  true
                      && 0 <= j₁₆
                      && j₁₆ <= 100000
                      && (forall x₅: int ::
                            ((exists j₄: int ::
                                    x₅ == j₄
                                    && 0 <= j₄
                                    && j₄ < j₁₆)
                               ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                                      j₄ < 100000
                                      && x₅ == j₄
                                      && 0 <= j₄
                                      && j₄ < j₁₆
                                      && src₁₅[x₅] == __VERIFIER_nondet_int₁₃)))
                      && (forall x₅: int ::
                            (!((exists j₄: int ::
                                    x₅ == j₄
                                    && 0 <= j₄
                                    && j₄ < j₁₆)
                            )
                               ==> src₁₅[x₅] == src[x₅]))
                      && (forall j₄: int ::
                            (  j₄ <= j₄
                              && 0 <= j₄
                              && j₄ < j₁₆
                               ==> j₄ < 100000))
                       ==> (j₁₆ < 100000
                           ==> (forall __VERIFIER_nondet_int₁: int ::
                                  true
                                  && 0 <= j₁₆ + 1
                                  && j₁₆ + 1 <= 100000
                                  && (forall x₅: int ::
                                        ((exists j₄: int ::
                                                x₅ == j₄
                                                && 0 <= j₄
                                                && j₄ < j₁₆ + 1)
                                           ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                                                  j₄ < 100000
                                                  && x₅ == j₄
                                                  && 0 <= j₄
                                                  && j₄ < j₁₆ + 1
                                                  && src₁₅[j₁₆ := __VERIFIER_nondet_int₁][x₅] == __VERIFIER_nondet_int₁₃)))
                                  && (forall x₅: int ::
                                        (!((exists j₄: int ::
                                                x₅ == j₄
                                                && 0 <= j₄
                                                && j₄ < j₁₆ + 1)
                                        )
                                           ==> src₁₅[j₁₆ := __VERIFIER_nondet_int₁][x₅] == src[x₅]))
                                  && (forall j₄: int ::
                                        (  j₄ <= j₄
                                          && 0 <= j₄
                                          && j₄ < j₁₆ + 1
                                           ==> j₄ < 100000))
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
                                && (forall x₉: int ::
                                      ((exists i₈: int ::
                                              x₉ == i₈
                                              && 0 <= i₈
                                              && i₈ < 0)
                                         ==> (exists i₈: int ::
                                                i₈ < 100000
                                                && src₁₅[i₈] != 0
                                                && x₉ == i₈
                                                && 0 <= i₈
                                                && i₈ < 0
                                                && dst[x₉] == src₁₅[i₈])))
                                && (forall x₉: int ::
                                      (!((exists i₈: int ::
                                              x₉ == i₈
                                              && 0 <= i₈
                                              && i₈ < 0)
                                      )
                                         ==> dst[x₉] == dst[x₉]))
                                && (forall i₈: int ::
                                      (  i₈ <= i₈
                                        && 0 <= i₈
                                        && i₈ < 0
                                         ==> i₈ < 100000
                                          && src₁₅[i₈] != 0))
                                && (forall dst₁₇: [int]int, i₁₈: int ::
                                      (  true
                                        && 0 <= i₁₈
                                        && i₁₈ <= 100000
                                        && (forall x₉: int ::
                                              ((exists i₈: int ::
                                                      x₉ == i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₈)
                                                 ==> (exists i₈: int ::
                                                        i₈ < 100000
                                                        && src₁₅[i₈] != 0
                                                        && x₉ == i₈
                                                        && 0 <= i₈
                                                        && i₈ < i₁₈
                                                        && dst₁₇[x₉] == src₁₅[i₈])))
                                        && (forall x₉: int ::
                                              (!((exists i₈: int ::
                                                      x₉ == i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₈)
                                              )
                                                 ==> dst₁₇[x₉] == dst[x₉]))
                                        && (forall i₈: int ::
                                              (  i₈ <= i₈
                                                && 0 <= i₈
                                                && i₈ < i₁₈
                                                 ==> i₈ < 100000
                                                  && src₁₅[i₈] != 0))
                                         ==> (  i₁₈ < 100000
                                            && src₁₅[i₁₈] != 0
                                             ==> true
                                              && 0 <= i₁₈ + 1
                                              && i₁₈ + 1 <= 100000
                                              && (forall x₉: int ::
                                                    ((exists i₈: int ::
                                                            x₉ == i₈
                                                            && 0 <= i₈
                                                            && i₈ < i₁₈ + 1)
                                                       ==> (exists i₈: int ::
                                                              i₈ < 100000
                                                              && src₁₅[i₈] != 0
                                                              && x₉ == i₈
                                                              && 0 <= i₈
                                                              && i₈ < i₁₈ + 1
                                                              && dst₁₇[i₁₈ := src₁₅[i₁₈]][x₉] == src₁₅[i₈])))
                                              && (forall x₉: int ::
                                                    (!((exists i₈: int ::
                                                            x₉ == i₈
                                                            && 0 <= i₈
                                                            && i₈ < i₁₈ + 1)
                                                    )
                                                       ==> dst₁₇[i₁₈ := src₁₅[i₁₈]][x₉] == dst[x₉]))
                                              && (forall i₈: int ::
                                                    (  i₈ <= i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₈ + 1
                                                       ==> i₈ < 100000
                                                        && src₁₅[i₈] != 0))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (!(  i₁₈ < 100000
                                            && src₁₅[i₁₈] != 0
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= i₁₈
                                                  && (forall x₁₃: int ::
                                                        (  x₁₃ <= x₁₃
                                                          && 0 <= x₁₃
                                                          && x₁₃ < 0
                                                           ==> x₁₃ < i₁₈))
                                                  && (forall x₁₉: int ::
                                                        (  true
                                                          && 0 <= x₁₉
                                                          && x₁₉ <= i₁₈
                                                          && (forall x₁₃: int ::
                                                                (  x₁₃ <= x₁₃
                                                                  && 0 <= x₁₃
                                                                  && x₁₃ < x₁₉
                                                                   ==> x₁₃ < i₁₈))
                                                           ==> (x₁₉ < i₁₈
                                                               ==> dst₁₇[x₁₉] == src₁₅[x₁₉]
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= x₁₉ + 1
                                                                    && x₁₉ + 1 <= i₁₈
                                                                    && (forall x₁₃: int ::
                                                                          (  x₁₃ <= x₁₃
                                                                            && 0 <= x₁₃
                                                                            && x₁₃ < x₁₉ + 1
                                                                             ==> x₁₃ < i₁₈))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(x₁₉ < i₁₈
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true))))))))))))));


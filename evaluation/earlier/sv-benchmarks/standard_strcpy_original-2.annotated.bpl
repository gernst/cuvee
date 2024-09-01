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
              && (forall src₁₄: [int]int, j₁₅: int ::
                    (  true
                      && 0 <= j₁₅
                      && j₁₅ <= 100000
                      && (forall x₅: int ::
                            ((exists j₄: int ::
                                    x₅ == j₄
                                    && 0 <= j₄
                                    && j₄ < j₁₅)
                               ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                                      j₄ < 100000
                                      && x₅ == j₄
                                      && 0 <= j₄
                                      && j₄ < j₁₅
                                      && src₁₄[x₅] == __VERIFIER_nondet_int₁₃)))
                      && (forall x₅: int ::
                            (!((exists j₄: int ::
                                    x₅ == j₄
                                    && 0 <= j₄
                                    && j₄ < j₁₅)
                            )
                               ==> src₁₄[x₅] == src[x₅]))
                      && (forall j₄: int ::
                            (  j₄ <= j₄
                              && 0 <= j₄
                              && j₄ < j₁₅
                               ==> j₄ < 100000))
                       ==> (j₁₅ < 100000
                           ==> (forall __VERIFIER_nondet_int₁: int ::
                                  true
                                  && 0 <= j₁₅ + 1
                                  && j₁₅ + 1 <= 100000
                                  && (forall x₅: int ::
                                        ((exists j₄: int ::
                                                x₅ == j₄
                                                && 0 <= j₄
                                                && j₄ < j₁₅ + 1)
                                           ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                                                  j₄ < 100000
                                                  && x₅ == j₄
                                                  && 0 <= j₄
                                                  && j₄ < j₁₅ + 1
                                                  && src₁₄[j₁₅ := __VERIFIER_nondet_int₁][x₅] == __VERIFIER_nondet_int₁₃)))
                                  && (forall x₅: int ::
                                        (!((exists j₄: int ::
                                                x₅ == j₄
                                                && 0 <= j₄
                                                && j₄ < j₁₅ + 1)
                                        )
                                           ==> src₁₄[j₁₅ := __VERIFIER_nondet_int₁][x₅] == src[x₅]))
                                  && (forall j₄: int ::
                                        (  j₄ <= j₄
                                          && 0 <= j₄
                                          && j₄ < j₁₅ + 1
                                           ==> j₄ < 100000))
                                  && true
                                  && (true
                                     ==> true)))
                        && (!(j₁₅ < 100000
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
                                                && src₁₄[i₈] != 0
                                                && x₉ == i₈
                                                && 0 <= i₈
                                                && i₈ < 0
                                                && dst[x₉] == src₁₄[i₈])))
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
                                          && src₁₄[i₈] != 0))
                                && (forall dst₁₆: [int]int, i₁₇: int ::
                                      (  true
                                        && 0 <= i₁₇
                                        && i₁₇ <= 100000
                                        && (forall x₉: int ::
                                              ((exists i₈: int ::
                                                      x₉ == i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₇)
                                                 ==> (exists i₈: int ::
                                                        i₈ < 100000
                                                        && src₁₄[i₈] != 0
                                                        && x₉ == i₈
                                                        && 0 <= i₈
                                                        && i₈ < i₁₇
                                                        && dst₁₆[x₉] == src₁₄[i₈])))
                                        && (forall x₉: int ::
                                              (!((exists i₈: int ::
                                                      x₉ == i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₇)
                                              )
                                                 ==> dst₁₆[x₉] == dst[x₉]))
                                        && (forall i₈: int ::
                                              (  i₈ <= i₈
                                                && 0 <= i₈
                                                && i₈ < i₁₇
                                                 ==> i₈ < 100000
                                                  && src₁₄[i₈] != 0))
                                         ==> (  i₁₇ < 100000
                                            && src₁₄[i₁₇] != 0
                                             ==> true
                                              && 0 <= i₁₇ + 1
                                              && i₁₇ + 1 <= 100000
                                              && (forall x₉: int ::
                                                    ((exists i₈: int ::
                                                            x₉ == i₈
                                                            && 0 <= i₈
                                                            && i₈ < i₁₇ + 1)
                                                       ==> (exists i₈: int ::
                                                              i₈ < 100000
                                                              && src₁₄[i₈] != 0
                                                              && x₉ == i₈
                                                              && 0 <= i₈
                                                              && i₈ < i₁₇ + 1
                                                              && dst₁₆[i₁₇ := src₁₄[i₁₇]][x₉] == src₁₄[i₈])))
                                              && (forall x₉: int ::
                                                    (!((exists i₈: int ::
                                                            x₉ == i₈
                                                            && 0 <= i₈
                                                            && i₈ < i₁₇ + 1)
                                                    )
                                                       ==> dst₁₆[i₁₇ := src₁₄[i₁₇]][x₉] == dst[x₉]))
                                              && (forall i₈: int ::
                                                    (  i₈ <= i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₇ + 1
                                                       ==> i₈ < 100000
                                                        && src₁₄[i₈] != 0))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (!(  i₁₇ < 100000
                                            && src₁₄[i₁₇] != 0
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= 100000
                                                  && (forall i₁₂: int ::
                                                        (  i₁₂ <= i₁₂
                                                          && 0 <= i₁₂
                                                          && i₁₂ < 0
                                                           ==> i₁₂ < 100000
                                                            && src₁₄[i₁₂] != 0))
                                                  && (forall i₁₈: int ::
                                                        (  true
                                                          && 0 <= i₁₈
                                                          && i₁₈ <= 100000
                                                          && (forall i₁₂: int ::
                                                                (  i₁₂ <= i₁₂
                                                                  && 0 <= i₁₂
                                                                  && i₁₂ < i₁₈
                                                                   ==> i₁₂ < 100000
                                                                    && src₁₄[i₁₂] != 0))
                                                           ==> (  i₁₈ < 100000
                                                              && src₁₄[i₁₈] != 0
                                                               ==> dst₁₆[i₁₈] == src₁₄[i₁₈]
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= i₁₈ + 1
                                                                    && i₁₈ + 1 <= 100000
                                                                    && (forall i₁₂: int ::
                                                                          (  i₁₂ <= i₁₂
                                                                            && 0 <= i₁₂
                                                                            && i₁₂ < i₁₈ + 1
                                                                             ==> i₁₂ < 100000
                                                                              && src₁₄[i₁₂] != 0))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(  i₁₈ < 100000
                                                              && src₁₄[i₁₈] != 0
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall i: int ::
        i % 2 == 0
        && (true
           ==> true));

goal (forall i: int ::
        i % 2 != 0
        && (true
           ==> true));

goal (forall array: [int]int ::
      (forall __VERIFIER_nondet_int₁: int ::
              true
              && 0 <= 0
              && 0 <= __VERIFIER_nondet_int₁
              && (forall x₇: int ::
                    ((exists i₆: int ::
                            x₇ == i₆
                            && 0 <= i₆
                            && i₆ < 0)
                       ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                              i₆ < __VERIFIER_nondet_int₁
                              && x₇ == i₆
                              && 0 <= i₆
                              && i₆ < 0
                              && array[x₇] == __VERIFIER_nondet_int₂₅)))
              && (forall x₇: int ::
                    (!((exists i₆: int ::
                            x₇ == i₆
                            && 0 <= i₆
                            && i₆ < 0)
                    )
                       ==> array[x₇] == array[x₇]))
              && (forall i₆: int ::
                    (  i₆ <= i₆
                      && 0 <= i₆
                      && i₆ < 0
                       ==> i₆ < __VERIFIER_nondet_int₁))
              && (forall array₁₆: [int]int, i₁₇: int ::
                    (  true
                      && 0 <= i₁₇
                      && i₁₇ <= __VERIFIER_nondet_int₁
                      && (forall x₇: int ::
                            ((exists i₆: int ::
                                    x₇ == i₆
                                    && 0 <= i₆
                                    && i₆ < i₁₇)
                               ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                                      i₆ < __VERIFIER_nondet_int₁
                                      && x₇ == i₆
                                      && 0 <= i₆
                                      && i₆ < i₁₇
                                      && array₁₆[x₇] == __VERIFIER_nondet_int₂₅)))
                      && (forall x₇: int ::
                            (!((exists i₆: int ::
                                    x₇ == i₆
                                    && 0 <= i₆
                                    && i₆ < i₁₇)
                            )
                               ==> array₁₆[x₇] == array[x₇]))
                      && (forall i₆: int ::
                            (  i₆ <= i₆
                              && 0 <= i₆
                              && i₆ < i₁₇
                               ==> i₆ < __VERIFIER_nondet_int₁))
                       ==> (i₁₇ < __VERIFIER_nondet_int₁
                           ==> (forall __VERIFIER_nondet_int₂: int ::
                                  true
                                  && 0 <= i₁₇ + 1
                                  && i₁₇ + 1 <= __VERIFIER_nondet_int₁
                                  && (forall x₇: int ::
                                        ((exists i₆: int ::
                                                x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₁₇ + 1)
                                           ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                                                  i₆ < __VERIFIER_nondet_int₁
                                                  && x₇ == i₆
                                                  && 0 <= i₆
                                                  && i₆ < i₁₇ + 1
                                                  && array₁₆[i₁₇ := __VERIFIER_nondet_int₂][x₇] == __VERIFIER_nondet_int₂₅)))
                                  && (forall x₇: int ::
                                        (!((exists i₆: int ::
                                                x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₁₇ + 1)
                                        )
                                           ==> array₁₆[i₁₇ := __VERIFIER_nondet_int₂][x₇] == array[x₇]))
                                  && (forall i₆: int ::
                                        (  i₆ <= i₆
                                          && 0 <= i₆
                                          && i₆ < i₁₇ + 1
                                           ==> i₆ < __VERIFIER_nondet_int₁))
                                  && true
                                  && (true
                                     ==> true)))
                        && (!(i₁₇ < __VERIFIER_nondet_int₁
                        )
                           ==> true
                            && (true
                               ==> true
                                && 0 <= 0
                                && 0 <= __VERIFIER_nondet_int₁
                                && (forall i₁₁: int ::
                                      (  i₁₁ <= i₁₁
                                        && 0 <= i₁₁
                                        && i₁₁ < 0
                                         ==> i₁₁ < __VERIFIER_nondet_int₁))
                                && (forall i₁₈: int ::
                                      (  true
                                        && 0 <= i₁₈
                                        && i₁₈ <= __VERIFIER_nondet_int₁
                                        && (forall i₁₁: int ::
                                              (  i₁₁ <= i₁₁
                                                && 0 <= i₁₁
                                                && i₁₁ < i₁₈
                                                 ==> i₁₁ < __VERIFIER_nondet_int₁))
                                         ==> (i₁₈ < __VERIFIER_nondet_int₁
                                             ==> (array₁₆[i₁₈] % 2 == 0
                                                 ==> true
                                                  && (true
                                                     ==> array₁₆[i₁₈] % 2 == 0
                                                      && (true
                                                         ==> true
                                                          && 0 <= i₁₈ + 1
                                                          && i₁₈ + 1 <= __VERIFIER_nondet_int₁
                                                          && (forall i₁₁: int ::
                                                                (  i₁₁ <= i₁₁
                                                                  && 0 <= i₁₁
                                                                  && i₁₁ < i₁₈ + 1
                                                                   ==> i₁₁ < __VERIFIER_nondet_int₁))
                                                          && true
                                                          && (true
                                                             ==> true))))
                                              && (array₁₆[i₁₈] % 2 != 0
                                                 ==> true
                                                  && 0 <= i₁₈ + 1
                                                  && i₁₈ + 1 <= __VERIFIER_nondet_int₁
                                                  && (forall i₁₁: int ::
                                                        (  i₁₁ <= i₁₁
                                                          && 0 <= i₁₁
                                                          && i₁₁ < i₁₈ + 1
                                                           ==> i₁₁ < __VERIFIER_nondet_int₁))
                                                  && true
                                                  && (true
                                                     ==> true)))
                                          && (!(i₁₈ < __VERIFIER_nondet_int₁
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= __VERIFIER_nondet_int₁
                                                  && (forall i₁₄: int ::
                                                        (  i₁₄ <= i₁₄
                                                          && 0 <= i₁₄
                                                          && i₁₄ < 0
                                                           ==> i₁₄ < __VERIFIER_nondet_int₁))
                                                  && (forall i₁₉: int ::
                                                        (  true
                                                          && 0 <= i₁₉
                                                          && i₁₉ <= __VERIFIER_nondet_int₁
                                                          && (forall i₁₄: int ::
                                                                (  i₁₄ <= i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < i₁₉
                                                                   ==> i₁₄ < __VERIFIER_nondet_int₁))
                                                           ==> (i₁₉ < __VERIFIER_nondet_int₁
                                                               ==> (array₁₆[i₁₉] % 2 != 0
                                                                   ==> true
                                                                    && (true
                                                                       ==> array₁₆[i₁₉] % 2 != 0
                                                                        && (true
                                                                           ==> true
                                                                            && 0 <= i₁₉ + 1
                                                                            && i₁₉ + 1 <= __VERIFIER_nondet_int₁
                                                                            && (forall i₁₄: int ::
                                                                                  (  i₁₄ <= i₁₄
                                                                                    && 0 <= i₁₄
                                                                                    && i₁₄ < i₁₉ + 1
                                                                                     ==> i₁₄ < __VERIFIER_nondet_int₁))
                                                                            && true
                                                                            && (true
                                                                               ==> true))))
                                                                && (!(array₁₆[i₁₉] % 2 != 0
                                                                )
                                                                   ==> true
                                                                    && 0 <= i₁₉ + 1
                                                                    && i₁₉ + 1 <= __VERIFIER_nondet_int₁
                                                                    && (forall i₁₄: int ::
                                                                          (  i₁₄ <= i₁₄
                                                                            && 0 <= i₁₄
                                                                            && i₁₄ < i₁₉ + 1
                                                                             ==> i₁₄ < __VERIFIER_nondet_int₁))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(i₁₉ < __VERIFIER_nondet_int₁
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int ::
        true
        && (1 < __VERIFIER_nondet_int₁
           ==> (forall a: [int]int ::
                  true
                  && 0 <= 0
                  && 0 <= __VERIFIER_nondet_int₁
                  && (forall x₆: int ::
                        ((exists i₅: int ::
                                x₆ == i₅
                                && 0 <= i₅
                                && i₅ < 0)
                           ==> (exists i₅: int ::
                                  i₅ < __VERIFIER_nondet_int₁
                                  && x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0
                                  && a[x₆] == -1 + i₅ * i₅)))
                  && (forall x₆: int ::
                        (!((exists i₅: int ::
                                x₆ == i₅
                                && 0 <= i₅
                                && i₅ < 0)
                        )
                           ==> a[x₆] == a[x₆]))
                  && (forall i₅: int ::
                        (  i₅ <= i₅
                          && 0 <= i₅
                          && i₅ < 0
                           ==> i₅ < __VERIFIER_nondet_int₁))
                  && (forall a₁₅: [int]int, i₁₆: int ::
                        (  true
                          && 0 <= i₁₆
                          && i₁₆ <= __VERIFIER_nondet_int₁
                          && (forall x₆: int ::
                                ((exists i₅: int ::
                                        x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₁₆)
                                   ==> (exists i₅: int ::
                                          i₅ < __VERIFIER_nondet_int₁
                                          && x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₆
                                          && a₁₅[x₆] == -1 + i₅ * i₅)))
                          && (forall x₆: int ::
                                (!((exists i₅: int ::
                                        x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₁₆)
                                )
                                   ==> a₁₅[x₆] == a[x₆]))
                          && (forall i₅: int ::
                                (  i₅ <= i₅
                                  && 0 <= i₅
                                  && i₅ < i₁₆
                                   ==> i₅ < __VERIFIER_nondet_int₁))
                           ==> (i₁₆ < __VERIFIER_nondet_int₁
                               ==> true
                                && 0 <= i₁₆ + 1
                                && i₁₆ + 1 <= __VERIFIER_nondet_int₁
                                && (forall x₆: int ::
                                      ((exists i₅: int ::
                                              x₆ == i₅
                                              && 0 <= i₅
                                              && i₅ < i₁₆ + 1)
                                         ==> (exists i₅: int ::
                                                i₅ < __VERIFIER_nondet_int₁
                                                && x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₆ + 1
                                                && a₁₅[i₁₆ := (i₁₆ - 1) * (i₁₆ + 1)][x₆] == -1 + i₅ * i₅)))
                                && (forall x₆: int ::
                                      (!((exists i₅: int ::
                                              x₆ == i₅
                                              && 0 <= i₅
                                              && i₅ < i₁₆ + 1)
                                      )
                                         ==> a₁₅[i₁₆ := (i₁₆ - 1) * (i₁₆ + 1)][x₆] == a[x₆]))
                                && (forall i₅: int ::
                                      (  i₅ <= i₅
                                        && 0 <= i₅
                                        && i₅ < i₁₆ + 1
                                         ==> i₅ < __VERIFIER_nondet_int₁))
                                && true
                                && (true
                                   ==> true))
                            && (!(i₁₆ < __VERIFIER_nondet_int₁
                            )
                               ==> true
                                && (true
                                   ==> true
                                    && 0 <= 0
                                    && 0 <= __VERIFIER_nondet_int₁
                                    && (forall x₁₀: int ::
                                          ((exists i₉: int ::
                                                  x₁₀ == i₉
                                                  && 0 <= i₉
                                                  && i₉ < 0)
                                             ==> (exists i₉: int ::
                                                    i₉ < __VERIFIER_nondet_int₁
                                                    && x₁₀ == i₉
                                                    && 0 <= i₉
                                                    && i₉ < 0
                                                    && a₁₅[x₁₀] == a₁₅[i₉] + -(i₉ * i₉))))
                                    && (forall x₁₀: int ::
                                          (!((exists i₉: int ::
                                                  x₁₀ == i₉
                                                  && 0 <= i₉
                                                  && i₉ < 0)
                                          )
                                             ==> a₁₅[x₁₀] == a₁₅[x₁₀]))
                                    && (forall i₉: int ::
                                          (  i₉ <= i₉
                                            && 0 <= i₉
                                            && i₉ < 0
                                             ==> i₉ < __VERIFIER_nondet_int₁))
                                    && (forall a₁₇: [int]int, i₁₈: int ::
                                          (  true
                                            && 0 <= i₁₈
                                            && i₁₈ <= __VERIFIER_nondet_int₁
                                            && (forall x₁₀: int ::
                                                  ((exists i₉: int ::
                                                          x₁₀ == i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₁₈)
                                                     ==> (exists i₉: int ::
                                                            i₉ < __VERIFIER_nondet_int₁
                                                            && x₁₀ == i₉
                                                            && 0 <= i₉
                                                            && i₉ < i₁₈
                                                            && a₁₇[x₁₀] == a₁₅[i₉] + -(i₉ * i₉))))
                                            && (forall x₁₀: int ::
                                                  (!((exists i₉: int ::
                                                          x₁₀ == i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₁₈)
                                                  )
                                                     ==> a₁₇[x₁₀] == a₁₅[x₁₀]))
                                            && (forall i₉: int ::
                                                  (  i₉ <= i₉
                                                    && 0 <= i₉
                                                    && i₉ < i₁₈
                                                     ==> i₉ < __VERIFIER_nondet_int₁))
                                             ==> (i₁₈ < __VERIFIER_nondet_int₁
                                                 ==> true
                                                  && 0 <= i₁₈ + 1
                                                  && i₁₈ + 1 <= __VERIFIER_nondet_int₁
                                                  && (forall x₁₀: int ::
                                                        ((exists i₉: int ::
                                                                x₁₀ == i₉
                                                                && 0 <= i₉
                                                                && i₉ < i₁₈ + 1)
                                                           ==> (exists i₉: int ::
                                                                  i₉ < __VERIFIER_nondet_int₁
                                                                  && x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₁₈ + 1
                                                                  && a₁₇[i₁₈ := a₁₇[i₁₈] - i₁₈ * i₁₈][x₁₀] == a₁₅[i₉] + -(i₉ * i₉))))
                                                  && (forall x₁₀: int ::
                                                        (!((exists i₉: int ::
                                                                x₁₀ == i₉
                                                                && 0 <= i₉
                                                                && i₉ < i₁₈ + 1)
                                                        )
                                                           ==> a₁₇[i₁₈ := a₁₇[i₁₈] - i₁₈ * i₁₈][x₁₀] == a₁₅[x₁₀]))
                                                  && (forall i₉: int ::
                                                        (  i₉ <= i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₁₈ + 1
                                                           ==> i₉ < __VERIFIER_nondet_int₁))
                                                  && true
                                                  && (true
                                                     ==> true))
                                              && (!(i₁₈ < __VERIFIER_nondet_int₁
                                              )
                                                 ==> true
                                                  && (true
                                                     ==> true
                                                      && 0 <= 0
                                                      && 0 <= __VERIFIER_nondet_int₁
                                                      && (forall i₁₃: int ::
                                                            (  i₁₃ <= i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < 0
                                                               ==> i₁₃ < __VERIFIER_nondet_int₁))
                                                      && (forall i₁₉: int ::
                                                            (  true
                                                              && 0 <= i₁₉
                                                              && i₁₉ <= __VERIFIER_nondet_int₁
                                                              && (forall i₁₃: int ::
                                                                    (  i₁₃ <= i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₁₉
                                                                       ==> i₁₃ < __VERIFIER_nondet_int₁))
                                                               ==> (i₁₉ < __VERIFIER_nondet_int₁
                                                                   ==> a₁₇[i₁₉] == -1
                                                                    && (true
                                                                       ==> true
                                                                        && 0 <= i₁₉ + 1
                                                                        && i₁₉ + 1 <= __VERIFIER_nondet_int₁
                                                                        && (forall i₁₃: int ::
                                                                              (  i₁₃ <= i₁₃
                                                                                && 0 <= i₁₃
                                                                                && i₁₃ < i₁₉ + 1
                                                                                 ==> i₁₃ < __VERIFIER_nondet_int₁))
                                                                        && true
                                                                        && (true
                                                                           ==> true)))
                                                                && (!(i₁₉ < __VERIFIER_nondet_int₁
                                                                )
                                                                   ==> true
                                                                    && (true
                                                                       ==> true)))))))))))))));


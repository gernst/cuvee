data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
      (forall __VERIFIER_nondet_int₁: int ::
            (forall __VERIFIER_nondet_int₂: int ::
                    true
                    && 0 <= 0
                    && 0 <= 100000
                    && (forall x₈: int ::
                          ((exists i₇: int ::
                                  x₈ == i₇
                                  && 0 <= i₇
                                  && i₇ < 0)
                             ==> (exists __VERIFIER_nondet_int₃₆: int, i₇: int ::
                                    i₇ < 100000
                                    && x₈ == i₇
                                    && 0 <= i₇
                                    && i₇ < 0
                                    && a[x₈] == __VERIFIER_nondet_int₃₆)))
                    && (forall x₈: int ::
                          (!((exists i₇: int ::
                                  x₈ == i₇
                                  && 0 <= i₇
                                  && i₇ < 0)
                          )
                             ==> a[x₈] == a[x₈]))
                    && (forall i₇: int ::
                          (  i₇ <= i₇
                            && 0 <= i₇
                            && i₇ < 0
                             ==> i₇ < 100000))
                    && (forall a₁₃: [int]int, i₁₄: int ::
                          (  true
                            && 0 <= i₁₄
                            && i₁₄ <= 100000
                            && (forall x₈: int ::
                                  ((exists i₇: int ::
                                          x₈ == i₇
                                          && 0 <= i₇
                                          && i₇ < i₁₄)
                                     ==> (exists __VERIFIER_nondet_int₃₆: int, i₇: int ::
                                            i₇ < 100000
                                            && x₈ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₁₄
                                            && a₁₃[x₈] == __VERIFIER_nondet_int₃₆)))
                            && (forall x₈: int ::
                                  (!((exists i₇: int ::
                                          x₈ == i₇
                                          && 0 <= i₇
                                          && i₇ < i₁₄)
                                  )
                                     ==> a₁₃[x₈] == a[x₈]))
                            && (forall i₇: int ::
                                  (  i₇ <= i₇
                                    && 0 <= i₇
                                    && i₇ < i₁₄
                                     ==> i₇ < 100000))
                             ==> (i₁₄ < 100000
                                 ==> (forall __VERIFIER_nondet_int₃: int ::
                                        true
                                        && 0 <= i₁₄ + 1
                                        && i₁₄ + 1 <= 100000
                                        && (forall x₈: int ::
                                              ((exists i₇: int ::
                                                      x₈ == i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₁₄ + 1)
                                                 ==> (exists __VERIFIER_nondet_int₃₆: int, i₇: int ::
                                                        i₇ < 100000
                                                        && x₈ == i₇
                                                        && 0 <= i₇
                                                        && i₇ < i₁₄ + 1
                                                        && a₁₃[i₁₄ := __VERIFIER_nondet_int₃][x₈] == __VERIFIER_nondet_int₃₆)))
                                        && (forall x₈: int ::
                                              (!((exists i₇: int ::
                                                      x₈ == i₇
                                                      && 0 <= i₇
                                                      && i₇ < i₁₄ + 1)
                                              )
                                                 ==> a₁₃[i₁₄ := __VERIFIER_nondet_int₃][x₈] == a[x₈]))
                                        && (forall i₇: int ::
                                              (  i₇ <= i₇
                                                && 0 <= i₇
                                                && i₇ < i₁₄ + 1
                                                 ==> i₇ < 100000))
                                        && true
                                        && (true
                                           ==> true)))
                              && (!(i₁₄ < 100000
                              )
                                 ==> true
                                  && (true
                                     ==> (  0 <= __VERIFIER_nondet_int₂
                                        && __VERIFIER_nondet_int₂ < 100000
                                         ==> true
                                          && 0 <= 0
                                          && (forall i₁₁: int ::
                                                (  i₁₁ <= i₁₁
                                                  && 0 <= i₁₁
                                                  && i₁₁ < 0
                                                   ==> a₁₃[__VERIFIER_nondet_int₂ := __VERIFIER_nondet_int₁][i₁₁] != __VERIFIER_nondet_int₁))
                                          && (forall i₁₆: int ::
                                                (  true
                                                  && 0 <= i₁₆
                                                  && (forall i₁₁: int ::
                                                        (  i₁₁ <= i₁₁
                                                          && 0 <= i₁₁
                                                          && i₁₁ < i₁₆
                                                           ==> a₁₃[__VERIFIER_nondet_int₂ := __VERIFIER_nondet_int₁][i₁₁] != __VERIFIER_nondet_int₁))
                                                   ==> (a₁₃[__VERIFIER_nondet_int₂ := __VERIFIER_nondet_int₁][i₁₆] != __VERIFIER_nondet_int₁
                                                       ==> true
                                                        && 0 <= i₁₆ + 1
                                                        && (forall i₁₁: int ::
                                                              (  i₁₁ <= i₁₁
                                                                && 0 <= i₁₁
                                                                && i₁₁ < i₁₆ + 1
                                                                 ==> a₁₃[__VERIFIER_nondet_int₂ := __VERIFIER_nondet_int₁][i₁₁] != __VERIFIER_nondet_int₁))
                                                        && true
                                                        && (true
                                                           ==> true))
                                                    && (!(a₁₃[__VERIFIER_nondet_int₂ := __VERIFIER_nondet_int₁][i₁₆] != __VERIFIER_nondet_int₁
                                                    )
                                                       ==> true
                                                        && (true
                                                           ==> i₁₆ <= __VERIFIER_nondet_int₂
                                                            && (true
                                                               ==> true))))))
                                      && (!(  0 <= __VERIFIER_nondet_int₂
                                        && __VERIFIER_nondet_int₂ < 100000
                                      )
                                         ==> true))))))));


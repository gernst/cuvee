data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
      (forall b: [int]int ::
            (forall c: [int]int ::
                    true
                    && 0 <= 0
                    && 0 <= 100000
                    && (forall x₇: int ::
                          ((exists i₆: int ::
                                  x₇ == i₆
                                  && 0 <= i₆
                                  && i₆ < 0)
                             ==> (exists __VERIFIER_nondet_int₁₄: int, i₆: int ::
                                    i₆ < 100000
                                    && x₇ == i₆
                                    && 0 <= i₆
                                    && i₆ < 0
                                    && a[x₇] == __VERIFIER_nondet_int₁₄)))
                    && (forall x₇: int ::
                          (!((exists i₆: int ::
                                  x₇ == i₆
                                  && 0 <= i₆
                                  && i₆ < 0)
                          )
                             ==> a[x₇] == a[x₇]))
                    && (forall x₈: int ::
                          ((exists i₆: int ::
                                  x₈ == i₆
                                  && 0 <= i₆
                                  && i₆ < 0)
                             ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                                    i₆ < 100000
                                    && x₈ == i₆
                                    && 0 <= i₆
                                    && i₆ < 0
                                    && b[x₈] == __VERIFIER_nondet_int₂₅)))
                    && (forall x₈: int ::
                          (!((exists i₆: int ::
                                  x₈ == i₆
                                  && 0 <= i₆
                                  && i₆ < 0)
                          )
                             ==> b[x₈] == b[x₈]))
                    && (forall i₆: int ::
                          (  i₆ <= i₆
                            && 0 <= i₆
                            && i₆ < 0
                             ==> i₆ < 100000))
                    && (forall a₁₉: [int]int, b₂₀: [int]int, i₂₁: int ::
                          (  true
                            && 0 <= i₂₁
                            && i₂₁ <= 100000
                            && (forall x₇: int ::
                                  ((exists i₆: int ::
                                          x₇ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₂₁)
                                     ==> (exists __VERIFIER_nondet_int₁₄: int, i₆: int ::
                                            i₆ < 100000
                                            && x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₂₁
                                            && a₁₉[x₇] == __VERIFIER_nondet_int₁₄)))
                            && (forall x₇: int ::
                                  (!((exists i₆: int ::
                                          x₇ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₂₁)
                                  )
                                     ==> a₁₉[x₇] == a[x₇]))
                            && (forall x₈: int ::
                                  ((exists i₆: int ::
                                          x₈ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₂₁)
                                     ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                                            i₆ < 100000
                                            && x₈ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₂₁
                                            && b₂₀[x₈] == __VERIFIER_nondet_int₂₅)))
                            && (forall x₈: int ::
                                  (!((exists i₆: int ::
                                          x₈ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₂₁)
                                  )
                                     ==> b₂₀[x₈] == b[x₈]))
                            && (forall i₆: int ::
                                  (  i₆ <= i₆
                                    && 0 <= i₆
                                    && i₆ < i₂₁
                                     ==> i₆ < 100000))
                             ==> (i₂₁ < 100000
                                 ==> (forall __VERIFIER_nondet_int₁: int ::
                                      (forall __VERIFIER_nondet_int₂: int ::
                                              true
                                              && 0 <= i₂₁ + 1
                                              && i₂₁ + 1 <= 100000
                                              && (forall x₇: int ::
                                                    ((exists i₆: int ::
                                                            x₇ == i₆
                                                            && 0 <= i₆
                                                            && i₆ < i₂₁ + 1)
                                                       ==> (exists __VERIFIER_nondet_int₁₄: int, i₆: int ::
                                                              i₆ < 100000
                                                              && x₇ == i₆
                                                              && 0 <= i₆
                                                              && i₆ < i₂₁ + 1
                                                              && a₁₉[i₂₁ := __VERIFIER_nondet_int₁][x₇] == __VERIFIER_nondet_int₁₄)))
                                              && (forall x₇: int ::
                                                    (!((exists i₆: int ::
                                                            x₇ == i₆
                                                            && 0 <= i₆
                                                            && i₆ < i₂₁ + 1)
                                                    )
                                                       ==> a₁₉[i₂₁ := __VERIFIER_nondet_int₁][x₇] == a[x₇]))
                                              && (forall x₈: int ::
                                                    ((exists i₆: int ::
                                                            x₈ == i₆
                                                            && 0 <= i₆
                                                            && i₆ < i₂₁ + 1)
                                                       ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                                                              i₆ < 100000
                                                              && x₈ == i₆
                                                              && 0 <= i₆
                                                              && i₆ < i₂₁ + 1
                                                              && b₂₀[i₂₁ := __VERIFIER_nondet_int₂][x₈] == __VERIFIER_nondet_int₂₅)))
                                              && (forall x₈: int ::
                                                    (!((exists i₆: int ::
                                                            x₈ == i₆
                                                            && 0 <= i₆
                                                            && i₆ < i₂₁ + 1)
                                                    )
                                                       ==> b₂₀[i₂₁ := __VERIFIER_nondet_int₂][x₈] == b[x₈]))
                                              && (forall i₆: int ::
                                                    (  i₆ <= i₆
                                                      && 0 <= i₆
                                                      && i₆ < i₂₁ + 1
                                                       ==> i₆ < 100000))
                                              && true
                                              && (true
                                                 ==> true))))
                              && (!(i₂₁ < 100000
                              )
                                 ==> true
                                  && (true
                                     ==> true
                                      && 0 <= 0
                                      && 0 <= 100000
                                      && (forall x₁₃: int ::
                                            ((exists i₁₂: int ::
                                                    x₁₃ == i₁₂
                                                    && 0 <= i₁₂
                                                    && i₁₂ < 0)
                                               ==> (exists i₁₂: int ::
                                                      i₁₂ < 100000
                                                      && x₁₃ == i₁₂
                                                      && 0 <= i₁₂
                                                      && i₁₂ < 0
                                                      && c[x₁₃] == a₁₉[i₁₂] + -b₂₀[i₁₂])))
                                      && (forall x₁₃: int ::
                                            (!((exists i₁₂: int ::
                                                    x₁₃ == i₁₂
                                                    && 0 <= i₁₂
                                                    && i₁₂ < 0)
                                            )
                                               ==> c[x₁₃] == c[x₁₃]))
                                      && (forall i₁₂: int ::
                                            (  i₁₂ <= i₁₂
                                              && 0 <= i₁₂
                                              && i₁₂ < 0
                                               ==> i₁₂ < 100000))
                                      && (forall c₂₂: [int]int, i₂₃: int ::
                                            (  true
                                              && 0 <= i₂₃
                                              && i₂₃ <= 100000
                                              && (forall x₁₃: int ::
                                                    ((exists i₁₂: int ::
                                                            x₁₃ == i₁₂
                                                            && 0 <= i₁₂
                                                            && i₁₂ < i₂₃)
                                                       ==> (exists i₁₂: int ::
                                                              i₁₂ < 100000
                                                              && x₁₃ == i₁₂
                                                              && 0 <= i₁₂
                                                              && i₁₂ < i₂₃
                                                              && c₂₂[x₁₃] == a₁₉[i₁₂] + -b₂₀[i₁₂])))
                                              && (forall x₁₃: int ::
                                                    (!((exists i₁₂: int ::
                                                            x₁₃ == i₁₂
                                                            && 0 <= i₁₂
                                                            && i₁₂ < i₂₃)
                                                    )
                                                       ==> c₂₂[x₁₃] == c[x₁₃]))
                                              && (forall i₁₂: int ::
                                                    (  i₁₂ <= i₁₂
                                                      && 0 <= i₁₂
                                                      && i₁₂ < i₂₃
                                                       ==> i₁₂ < 100000))
                                               ==> (i₂₃ < 100000
                                                   ==> true
                                                    && 0 <= i₂₃ + 1
                                                    && i₂₃ + 1 <= 100000
                                                    && (forall x₁₃: int ::
                                                          ((exists i₁₂: int ::
                                                                  x₁₃ == i₁₂
                                                                  && 0 <= i₁₂
                                                                  && i₁₂ < i₂₃ + 1)
                                                             ==> (exists i₁₂: int ::
                                                                    i₁₂ < 100000
                                                                    && x₁₃ == i₁₂
                                                                    && 0 <= i₁₂
                                                                    && i₁₂ < i₂₃ + 1
                                                                    && c₂₂[i₂₃ := a₁₉[i₂₃] - b₂₀[i₂₃]][x₁₃] == a₁₉[i₁₂] + -b₂₀[i₁₂])))
                                                    && (forall x₁₃: int ::
                                                          (!((exists i₁₂: int ::
                                                                  x₁₃ == i₁₂
                                                                  && 0 <= i₁₂
                                                                  && i₁₂ < i₂₃ + 1)
                                                          )
                                                             ==> c₂₂[i₂₃ := a₁₉[i₂₃] - b₂₀[i₂₃]][x₁₃] == c[x₁₃]))
                                                    && (forall i₁₂: int ::
                                                          (  i₁₂ <= i₁₂
                                                            && 0 <= i₁₂
                                                            && i₁₂ < i₂₃ + 1
                                                             ==> i₁₂ < 100000))
                                                    && true
                                                    && (true
                                                       ==> true))
                                                && (!(i₂₃ < 100000
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> true
                                                        && 0 <= 0
                                                        && 0 <= 100000
                                                        && (forall x₁₇: int ::
                                                              (  x₁₇ <= x₁₇
                                                                && 0 <= x₁₇
                                                                && x₁₇ < 0
                                                                 ==> x₁₇ < 100000))
                                                        && (forall x₂₄: int ::
                                                              (  true
                                                                && 0 <= x₂₄
                                                                && x₂₄ <= 100000
                                                                && (forall x₁₇: int ::
                                                                      (  x₁₇ <= x₁₇
                                                                        && 0 <= x₁₇
                                                                        && x₁₇ < x₂₄
                                                                         ==> x₁₇ < 100000))
                                                                 ==> (x₂₄ < 100000
                                                                     ==> c₂₂[x₂₄] == a₁₉[x₂₄] - b₂₀[x₂₄]
                                                                      && (true
                                                                         ==> true
                                                                          && 0 <= x₂₄ + 1
                                                                          && x₂₄ + 1 <= 100000
                                                                          && (forall x₁₇: int ::
                                                                                (  x₁₇ <= x₁₇
                                                                                  && 0 <= x₁₇
                                                                                  && x₁₇ < x₂₄ + 1
                                                                                   ==> x₁₇ < 100000))
                                                                          && true
                                                                          && (true
                                                                             ==> true)))
                                                                  && (!(x₂₄ < 100000
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true)))))))))))))));


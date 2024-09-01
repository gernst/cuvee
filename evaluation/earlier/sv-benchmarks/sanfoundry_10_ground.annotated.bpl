data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int ::
      (forall vectorx: [int]int ::
              true
              && 0 <= 0
              && 0 <= 100000
              && (forall x₈: int ::
                    ((exists i₇: int ::
                            x₈ == i₇
                            && 0 <= i₇
                            && i₇ < 0)
                       ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                              i₇ < 100000
                              && x₈ == i₇
                              && 0 <= i₇
                              && i₇ < 0
                              && vectorx[x₈] == __VERIFIER_nondet_int₂₆)))
              && (forall x₈: int ::
                    (!((exists i₇: int ::
                            x₈ == i₇
                            && 0 <= i₇
                            && i₇ < 0)
                    )
                       ==> vectorx[x₈] == vectorx[x₈]))
              && (forall i₇: int ::
                    (  i₇ <= i₇
                      && 0 <= i₇
                      && i₇ < 0
                       ==> i₇ < 100000))
              && (forall vectorx₂₆: [int]int, i₂₇: int ::
                    (  true
                      && 0 <= i₂₇
                      && i₂₇ <= 100000
                      && (forall x₈: int ::
                            ((exists i₇: int ::
                                    x₈ == i₇
                                    && 0 <= i₇
                                    && i₇ < i₂₇)
                               ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                                      i₇ < 100000
                                      && x₈ == i₇
                                      && 0 <= i₇
                                      && i₇ < i₂₇
                                      && vectorx₂₆[x₈] == __VERIFIER_nondet_int₂₆)))
                      && (forall x₈: int ::
                            (!((exists i₇: int ::
                                    x₈ == i₇
                                    && 0 <= i₇
                                    && i₇ < i₂₇)
                            )
                               ==> vectorx₂₆[x₈] == vectorx[x₈]))
                      && (forall i₇: int ::
                            (  i₇ <= i₇
                              && 0 <= i₇
                              && i₇ < i₂₇
                               ==> i₇ < 100000))
                       ==> (i₂₇ < 100000
                           ==> (forall __VERIFIER_nondet_int₂: int ::
                                  true
                                  && 0 <= i₂₇ + 1
                                  && i₂₇ + 1 <= 100000
                                  && (forall x₈: int ::
                                        ((exists i₇: int ::
                                                x₈ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₂₇ + 1)
                                           ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                                                  i₇ < 100000
                                                  && x₈ == i₇
                                                  && 0 <= i₇
                                                  && i₇ < i₂₇ + 1
                                                  && vectorx₂₆[i₂₇ := __VERIFIER_nondet_int₂][x₈] == __VERIFIER_nondet_int₂₆)))
                                  && (forall x₈: int ::
                                        (!((exists i₇: int ::
                                                x₈ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₂₇ + 1)
                                        )
                                           ==> vectorx₂₆[i₂₇ := __VERIFIER_nondet_int₂][x₈] == vectorx[x₈]))
                                  && (forall i₇: int ::
                                        (  i₇ <= i₇
                                          && 0 <= i₇
                                          && i₇ < i₂₇ + 1
                                           ==> i₇ < 100000))
                                  && true
                                  && (true
                                     ==> true)))
                        && (!(i₂₇ < 100000
                        )
                           ==> true
                            && (true
                               ==> true
                                && 0 <= 0
                                && 0 <= 100000
                                && (forall found₁₁: int, i₁₃: int ::
                                      (  i₁₃ <= i₁₃
                                        && 0 <= i₁₃
                                        && i₁₃ < 0
                                         ==> i₁₃ < 100000
                                          && found₁₁ == 0))
                                && (forall found₂₈: int, pos₂₉: int, i₃₀: int ::
                                      (  true
                                        && 0 <= i₃₀
                                        && i₃₀ <= 100000
                                        && (forall found₁₁: int, i₁₃: int ::
                                              (  i₁₃ <= i₁₃
                                                && 0 <= i₁₃
                                                && i₁₃ < i₃₀
                                                 ==> i₁₃ < 100000
                                                  && found₁₁ == 0))
                                         ==> (  i₃₀ < 100000
                                            && !(found₂₈ != 0
                                            )
                                             ==> (vectorx₂₆[i₃₀] == __VERIFIER_nondet_int₁
                                                 ==> true
                                                  && 0 <= i₃₀ + 1
                                                  && i₃₀ + 1 <= 100000
                                                  && (forall found₁₁: int, i₁₃: int ::
                                                        (  i₁₃ <= i₁₃
                                                          && 0 <= i₁₃
                                                          && i₁₃ < i₃₀ + 1
                                                           ==> i₁₃ < 100000
                                                            && found₁₁ == 0))
                                                  && true
                                                  && (true
                                                     ==> true))
                                              && (vectorx₂₆[i₃₀] != __VERIFIER_nondet_int₁
                                                 ==> true
                                                  && 0 <= i₃₀ + 1
                                                  && i₃₀ + 1 <= 100000
                                                  && (forall found₁₁: int, i₁₃: int ::
                                                        (  i₁₃ <= i₁₃
                                                          && 0 <= i₁₃
                                                          && i₁₃ < i₃₀ + 1
                                                           ==> i₁₃ < 100000
                                                            && found₁₁ == 0))
                                                  && true
                                                  && (true
                                                     ==> true)))
                                          && (!(  i₃₀ < 100000
                                            && !(found₂₈ != 0
                                            )
                                          )
                                             ==> true
                                              && (true
                                                 ==> (found₂₈ != 0
                                                     ==> true
                                                      && pos₂₉ <= pos₂₉
                                                      && pos₂₉ <= -1 + 100000
                                                      && (forall x₁₈: int ::
                                                            ((exists i₁₇: int ::
                                                                    x₁₈ == i₁₇
                                                                    && pos₂₉ <= i₁₇
                                                                    && i₁₇ < pos₂₉)
                                                               ==> (exists i₁₇: int ::
                                                                      i₁₇ < -1 + 100000
                                                                      && x₁₈ == i₁₇
                                                                      && pos₂₉ <= i₁₇
                                                                      && i₁₇ < pos₂₉
                                                                      && vectorx₂₆[x₁₈] == vectorx₂₆[1 + i₁₇])))
                                                      && (forall x₁₈: int ::
                                                            (!((exists i₁₇: int ::
                                                                    x₁₈ == i₁₇
                                                                    && pos₂₉ <= i₁₇
                                                                    && i₁₇ < pos₂₉)
                                                            )
                                                               ==> vectorx₂₆[x₁₈] == vectorx₂₆[x₁₈]))
                                                      && (forall i₁₇: int ::
                                                            (  i₁₇ <= i₁₇
                                                              && pos₂₉ <= i₁₇
                                                              && i₁₇ < pos₂₉
                                                               ==> i₁₇ < -1 + 100000))
                                                      && (forall vectorx₃₁: [int]int, i₃₂: int ::
                                                            (  true
                                                              && pos₂₉ <= i₃₂
                                                              && i₃₂ <= -1 + 100000
                                                              && (forall x₁₈: int ::
                                                                    ((exists i₁₇: int ::
                                                                            x₁₈ == i₁₇
                                                                            && pos₂₉ <= i₁₇
                                                                            && i₁₇ < i₃₂)
                                                                       ==> (exists i₁₇: int ::
                                                                              i₁₇ < -1 + 100000
                                                                              && x₁₈ == i₁₇
                                                                              && pos₂₉ <= i₁₇
                                                                              && i₁₇ < i₃₂
                                                                              && vectorx₃₁[x₁₈] == vectorx₂₆[1 + i₁₇])))
                                                              && (forall x₁₈: int ::
                                                                    (!((exists i₁₇: int ::
                                                                            x₁₈ == i₁₇
                                                                            && pos₂₉ <= i₁₇
                                                                            && i₁₇ < i₃₂)
                                                                    )
                                                                       ==> vectorx₃₁[x₁₈] == vectorx₂₆[x₁₈]))
                                                              && (forall i₁₇: int ::
                                                                    (  i₁₇ <= i₁₇
                                                                      && pos₂₉ <= i₁₇
                                                                      && i₁₇ < i₃₂
                                                                       ==> i₁₇ < -1 + 100000))
                                                               ==> (i₃₂ < 100000 - 1
                                                                   ==> true
                                                                    && pos₂₉ <= i₃₂ + 1
                                                                    && i₃₂ + 1 <= -1 + 100000
                                                                    && (forall x₁₈: int ::
                                                                          ((exists i₁₇: int ::
                                                                                  x₁₈ == i₁₇
                                                                                  && pos₂₉ <= i₁₇
                                                                                  && i₁₇ < i₃₂ + 1)
                                                                             ==> (exists i₁₇: int ::
                                                                                    i₁₇ < -1 + 100000
                                                                                    && x₁₈ == i₁₇
                                                                                    && pos₂₉ <= i₁₇
                                                                                    && i₁₇ < i₃₂ + 1
                                                                                    && vectorx₃₁[i₃₂ := vectorx₃₁[i₃₂ + 1]][x₁₈] == vectorx₂₆[1 + i₁₇])))
                                                                    && (forall x₁₈: int ::
                                                                          (!((exists i₁₇: int ::
                                                                                  x₁₈ == i₁₇
                                                                                  && pos₂₉ <= i₁₇
                                                                                  && i₁₇ < i₃₂ + 1)
                                                                          )
                                                                             ==> vectorx₃₁[i₃₂ := vectorx₃₁[i₃₂ + 1]][x₁₈] == vectorx₂₆[x₁₈]))
                                                                    && (forall i₁₇: int ::
                                                                          (  i₁₇ <= i₁₇
                                                                            && pos₂₉ <= i₁₇
                                                                            && i₁₇ < i₃₂ + 1
                                                                             ==> i₁₇ < -1 + 100000))
                                                                    && true
                                                                    && (true
                                                                       ==> true))
                                                                && (!(i₃₂ < 100000 - 1
                                                                )
                                                                   ==> true
                                                                    && (true
                                                                       ==> (found₂₈ != 0
                                                                           ==> true
                                                                            && 0 <= 0
                                                                            && 0 <= pos₂₉
                                                                            && (forall x₂₃: int ::
                                                                                  (  x₂₃ <= x₂₃
                                                                                    && 0 <= x₂₃
                                                                                    && x₂₃ < 0
                                                                                     ==> x₂₃ < pos₂₉))
                                                                            && (forall x₃₃: int ::
                                                                                  (  true
                                                                                    && 0 <= x₃₃
                                                                                    && x₃₃ <= pos₂₉
                                                                                    && (forall x₂₃: int ::
                                                                                          (  x₂₃ <= x₂₃
                                                                                            && 0 <= x₂₃
                                                                                            && x₂₃ < x₃₃
                                                                                             ==> x₂₃ < pos₂₉))
                                                                                     ==> (x₃₃ < pos₂₉
                                                                                         ==> vectorx₃₁[x₃₃] != __VERIFIER_nondet_int₁
                                                                                          && (true
                                                                                             ==> true
                                                                                              && 0 <= x₃₃ + 1
                                                                                              && x₃₃ + 1 <= pos₂₉
                                                                                              && (forall x₂₃: int ::
                                                                                                    (  x₂₃ <= x₂₃
                                                                                                      && 0 <= x₂₃
                                                                                                      && x₂₃ < x₃₃ + 1
                                                                                                       ==> x₂₃ < pos₂₉))
                                                                                              && true
                                                                                              && (true
                                                                                                 ==> true)))
                                                                                      && (!(x₃₃ < pos₂₉
                                                                                      )
                                                                                         ==> true
                                                                                          && (true
                                                                                             ==> true)))))
                                                                        && (!(found₂₈ != 0
                                                                        )
                                                                           ==> true))))))
                                                  && (!(found₂₈ != 0
                                                  )
                                                     ==> (found₂₈ != 0
                                                         ==> true
                                                          && 0 <= 0
                                                          && 0 <= pos₂₉
                                                          && (forall x₂₃: int ::
                                                                (  x₂₃ <= x₂₃
                                                                  && 0 <= x₂₃
                                                                  && x₂₃ < 0
                                                                   ==> x₂₃ < pos₂₉))
                                                          && (forall x₃₇: int ::
                                                                (  true
                                                                  && 0 <= x₃₇
                                                                  && x₃₇ <= pos₂₉
                                                                  && (forall x₂₃: int ::
                                                                        (  x₂₃ <= x₂₃
                                                                          && 0 <= x₂₃
                                                                          && x₂₃ < x₃₇
                                                                           ==> x₂₃ < pos₂₉))
                                                                   ==> (x₃₇ < pos₂₉
                                                                       ==> vectorx₂₆[x₃₇] != __VERIFIER_nondet_int₁
                                                                        && (true
                                                                           ==> true
                                                                            && 0 <= x₃₇ + 1
                                                                            && x₃₇ + 1 <= pos₂₉
                                                                            && (forall x₂₃: int ::
                                                                                  (  x₂₃ <= x₂₃
                                                                                    && 0 <= x₂₃
                                                                                    && x₂₃ < x₃₇ + 1
                                                                                     ==> x₂₃ < pos₂₉))
                                                                            && true
                                                                            && (true
                                                                               ==> true)))
                                                                    && (!(x₃₇ < pos₂₉
                                                                    )
                                                                       ==> true
                                                                        && (true
                                                                           ==> true)))))
                                                      && (!(found₂₈ != 0
                                                      )
                                                         ==> true))))))))))));


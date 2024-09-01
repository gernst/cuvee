data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int ::
      (forall a2: [int]int ::
            (forall a3: [int]int ::
                    true
                    && 0 <= 0
                    && 0 <= 200000
                    && (forall x₁₀: int ::
                          ((exists i₉: int ::
                                  x₁₀ == i₉
                                  && 0 <= i₉
                                  && i₉ < 0)
                             ==> (exists __VERIFIER_nondet_int₁₆: int, i₉: int ::
                                    i₉ < 200000
                                    && x₁₀ == i₉
                                    && 0 <= i₉
                                    && i₉ < 0
                                    && a1[x₁₀] == __VERIFIER_nondet_int₁₆)))
                    && (forall x₁₀: int ::
                          (!((exists i₉: int ::
                                  x₁₀ == i₉
                                  && 0 <= i₉
                                  && i₉ < 0)
                          )
                             ==> a1[x₁₀] == a1[x₁₀]))
                    && (forall x₁₁: int ::
                          ((exists i₉: int ::
                                  x₁₁ == i₉
                                  && 0 <= i₉
                                  && i₉ < 0)
                             ==> (exists __VERIFIER_nondet_int₂₇: int, i₉: int ::
                                    i₉ < 200000
                                    && x₁₁ == i₉
                                    && 0 <= i₉
                                    && i₉ < 0
                                    && a2[x₁₁] == __VERIFIER_nondet_int₂₇)))
                    && (forall x₁₁: int ::
                          (!((exists i₉: int ::
                                  x₁₁ == i₉
                                  && 0 <= i₉
                                  && i₉ < 0)
                          )
                             ==> a2[x₁₁] == a2[x₁₁]))
                    && (forall x₁₂: int ::
                          ((exists i₉: int ::
                                  x₁₂ == i₉
                                  && 0 <= i₉
                                  && i₉ < 0)
                             ==> (exists __VERIFIER_nondet_int₃₈: int, i₉: int ::
                                    i₉ < 200000
                                    && x₁₂ == i₉
                                    && 0 <= i₉
                                    && i₉ < 0
                                    && a3[x₁₂] == __VERIFIER_nondet_int₃₈)))
                    && (forall x₁₂: int ::
                          (!((exists i₉: int ::
                                  x₁₂ == i₉
                                  && 0 <= i₉
                                  && i₉ < 0)
                          )
                             ==> a3[x₁₂] == a3[x₁₂]))
                    && (forall i₉: int ::
                          (  i₉ <= i₉
                            && 0 <= i₉
                            && i₉ < 0
                             ==> i₉ < 200000))
                    && (forall a1₂₈: [int]int, a2₂₉: [int]int, a3₃₀: [int]int, i₃₁: int ::
                          (  true
                            && 0 <= i₃₁
                            && i₃₁ <= 200000
                            && (forall x₁₀: int ::
                                  ((exists i₉: int ::
                                          x₁₀ == i₉
                                          && 0 <= i₉
                                          && i₉ < i₃₁)
                                     ==> (exists __VERIFIER_nondet_int₁₆: int, i₉: int ::
                                            i₉ < 200000
                                            && x₁₀ == i₉
                                            && 0 <= i₉
                                            && i₉ < i₃₁
                                            && a1₂₈[x₁₀] == __VERIFIER_nondet_int₁₆)))
                            && (forall x₁₀: int ::
                                  (!((exists i₉: int ::
                                          x₁₀ == i₉
                                          && 0 <= i₉
                                          && i₉ < i₃₁)
                                  )
                                     ==> a1₂₈[x₁₀] == a1[x₁₀]))
                            && (forall x₁₁: int ::
                                  ((exists i₉: int ::
                                          x₁₁ == i₉
                                          && 0 <= i₉
                                          && i₉ < i₃₁)
                                     ==> (exists __VERIFIER_nondet_int₂₇: int, i₉: int ::
                                            i₉ < 200000
                                            && x₁₁ == i₉
                                            && 0 <= i₉
                                            && i₉ < i₃₁
                                            && a2₂₉[x₁₁] == __VERIFIER_nondet_int₂₇)))
                            && (forall x₁₁: int ::
                                  (!((exists i₉: int ::
                                          x₁₁ == i₉
                                          && 0 <= i₉
                                          && i₉ < i₃₁)
                                  )
                                     ==> a2₂₉[x₁₁] == a2[x₁₁]))
                            && (forall x₁₂: int ::
                                  ((exists i₉: int ::
                                          x₁₂ == i₉
                                          && 0 <= i₉
                                          && i₉ < i₃₁)
                                     ==> (exists __VERIFIER_nondet_int₃₈: int, i₉: int ::
                                            i₉ < 200000
                                            && x₁₂ == i₉
                                            && 0 <= i₉
                                            && i₉ < i₃₁
                                            && a3₃₀[x₁₂] == __VERIFIER_nondet_int₃₈)))
                            && (forall x₁₂: int ::
                                  (!((exists i₉: int ::
                                          x₁₂ == i₉
                                          && 0 <= i₉
                                          && i₉ < i₃₁)
                                  )
                                     ==> a3₃₀[x₁₂] == a3[x₁₂]))
                            && (forall i₉: int ::
                                  (  i₉ <= i₉
                                    && 0 <= i₉
                                    && i₉ < i₃₁
                                     ==> i₉ < 200000))
                             ==> (i₃₁ < 200000
                                 ==> (forall __VERIFIER_nondet_int₁: int ::
                                      (forall __VERIFIER_nondet_int₂: int ::
                                            (forall __VERIFIER_nondet_int₃: int ::
                                                    true
                                                    && 0 <= i₃₁ + 1
                                                    && i₃₁ + 1 <= 200000
                                                    && (forall x₁₀: int ::
                                                          ((exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₃₁ + 1)
                                                             ==> (exists __VERIFIER_nondet_int₁₆: int, i₉: int ::
                                                                    i₉ < 200000
                                                                    && x₁₀ == i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₃₁ + 1
                                                                    && a1₂₈[i₃₁ := __VERIFIER_nondet_int₁][x₁₀] == __VERIFIER_nondet_int₁₆)))
                                                    && (forall x₁₀: int ::
                                                          (!((exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₃₁ + 1)
                                                          )
                                                             ==> a1₂₈[i₃₁ := __VERIFIER_nondet_int₁][x₁₀] == a1[x₁₀]))
                                                    && (forall x₁₁: int ::
                                                          ((exists i₉: int ::
                                                                  x₁₁ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₃₁ + 1)
                                                             ==> (exists __VERIFIER_nondet_int₂₇: int, i₉: int ::
                                                                    i₉ < 200000
                                                                    && x₁₁ == i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₃₁ + 1
                                                                    && a2₂₉[i₃₁ := __VERIFIER_nondet_int₂][x₁₁] == __VERIFIER_nondet_int₂₇)))
                                                    && (forall x₁₁: int ::
                                                          (!((exists i₉: int ::
                                                                  x₁₁ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₃₁ + 1)
                                                          )
                                                             ==> a2₂₉[i₃₁ := __VERIFIER_nondet_int₂][x₁₁] == a2[x₁₁]))
                                                    && (forall x₁₂: int ::
                                                          ((exists i₉: int ::
                                                                  x₁₂ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₃₁ + 1)
                                                             ==> (exists __VERIFIER_nondet_int₃₈: int, i₉: int ::
                                                                    i₉ < 200000
                                                                    && x₁₂ == i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₃₁ + 1
                                                                    && a3₃₀[i₃₁ := __VERIFIER_nondet_int₃][x₁₂] == __VERIFIER_nondet_int₃₈)))
                                                    && (forall x₁₂: int ::
                                                          (!((exists i₉: int ::
                                                                  x₁₂ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₃₁ + 1)
                                                          )
                                                             ==> a3₃₀[i₃₁ := __VERIFIER_nondet_int₃][x₁₂] == a3[x₁₂]))
                                                    && (forall i₉: int ::
                                                          (  i₉ <= i₉
                                                            && 0 <= i₉
                                                            && i₉ < i₃₁ + 1
                                                             ==> i₉ < 200000))
                                                    && true
                                                    && (true
                                                       ==> true)))))
                              && (!(i₃₁ < 200000
                              )
                                 ==> true
                                  && (true
                                     ==> true
                                      && 0 <= 0
                                      && 0 <= 200000
                                      && (forall x₁₈: int ::
                                            ((exists i₁₇: int ::
                                                    x₁₈ == i₁₇
                                                    && 0 <= i₁₇
                                                    && i₁₇ < 0)
                                               ==> (exists i₁₇: int ::
                                                      i₁₇ != 150000
                                                      && i₁₇ < 200000
                                                      && x₁₈ == i₁₇
                                                      && 0 <= i₁₇
                                                      && i₁₇ < 0
                                                      && a2₂₉[x₁₈] == a1₂₈[i₁₇])))
                                      && (forall x₁₈: int ::
                                            (!((exists i₁₇: int ::
                                                    x₁₈ == i₁₇
                                                    && 0 <= i₁₇
                                                    && i₁₇ < 0)
                                            )
                                               ==> a2₂₉[x₁₈] == a2₂₉[x₁₈]))
                                      && (forall i₁₇: int ::
                                            (  i₁₇ <= i₁₇
                                              && 0 <= i₁₇
                                              && i₁₇ < 0
                                               ==> i₁₇ < 200000))
                                      && (forall a2₃₂: [int]int, i₃₃: int ::
                                            (  true
                                              && 0 <= i₃₃
                                              && i₃₃ <= 200000
                                              && (forall x₁₈: int ::
                                                    ((exists i₁₇: int ::
                                                            x₁₈ == i₁₇
                                                            && 0 <= i₁₇
                                                            && i₁₇ < i₃₃)
                                                       ==> (exists i₁₇: int ::
                                                              i₁₇ != 150000
                                                              && i₁₇ < 200000
                                                              && x₁₈ == i₁₇
                                                              && 0 <= i₁₇
                                                              && i₁₇ < i₃₃
                                                              && a2₃₂[x₁₈] == a1₂₈[i₁₇])))
                                              && (forall x₁₈: int ::
                                                    (!((exists i₁₇: int ::
                                                            x₁₈ == i₁₇
                                                            && 0 <= i₁₇
                                                            && i₁₇ < i₃₃)
                                                    )
                                                       ==> a2₃₂[x₁₈] == a2₂₉[x₁₈]))
                                              && (forall i₁₇: int ::
                                                    (  i₁₇ <= i₁₇
                                                      && 0 <= i₁₇
                                                      && i₁₇ < i₃₃
                                                       ==> i₁₇ < 200000))
                                               ==> (i₃₃ < 200000
                                                   ==> (i₃₃ != 150000
                                                       ==> true
                                                        && 0 <= i₃₃ + 1
                                                        && i₃₃ + 1 <= 200000
                                                        && (forall x₁₈: int ::
                                                              ((exists i₁₇: int ::
                                                                      x₁₈ == i₁₇
                                                                      && 0 <= i₁₇
                                                                      && i₁₇ < i₃₃ + 1)
                                                                 ==> (exists i₁₇: int ::
                                                                        i₁₇ != 150000
                                                                        && i₁₇ < 200000
                                                                        && x₁₈ == i₁₇
                                                                        && 0 <= i₁₇
                                                                        && i₁₇ < i₃₃ + 1
                                                                        && a2₃₂[i₃₃ := a1₂₈[i₃₃]][x₁₈] == a1₂₈[i₁₇])))
                                                        && (forall x₁₈: int ::
                                                              (!((exists i₁₇: int ::
                                                                      x₁₈ == i₁₇
                                                                      && 0 <= i₁₇
                                                                      && i₁₇ < i₃₃ + 1)
                                                              )
                                                                 ==> a2₃₂[i₃₃ := a1₂₈[i₃₃]][x₁₈] == a2₂₉[x₁₈]))
                                                        && (forall i₁₇: int ::
                                                              (  i₁₇ <= i₁₇
                                                                && 0 <= i₁₇
                                                                && i₁₇ < i₃₃ + 1
                                                                 ==> i₁₇ < 200000))
                                                        && true
                                                        && (true
                                                           ==> true))
                                                    && (!(i₃₃ != 150000
                                                    )
                                                       ==> true
                                                        && 0 <= i₃₃ + 1
                                                        && i₃₃ + 1 <= 200000
                                                        && (forall x₁₈: int ::
                                                              ((exists i₁₇: int ::
                                                                      x₁₈ == i₁₇
                                                                      && 0 <= i₁₇
                                                                      && i₁₇ < i₃₃ + 1)
                                                                 ==> (exists i₁₇: int ::
                                                                        i₁₇ != 150000
                                                                        && i₁₇ < 200000
                                                                        && x₁₈ == i₁₇
                                                                        && 0 <= i₁₇
                                                                        && i₁₇ < i₃₃ + 1
                                                                        && a2₃₂[x₁₈] == a1₂₈[i₁₇])))
                                                        && (forall x₁₈: int ::
                                                              (!((exists i₁₇: int ::
                                                                      x₁₈ == i₁₇
                                                                      && 0 <= i₁₇
                                                                      && i₁₇ < i₃₃ + 1)
                                                              )
                                                                 ==> a2₃₂[x₁₈] == a2₂₉[x₁₈]))
                                                        && (forall i₁₇: int ::
                                                              (  i₁₇ <= i₁₇
                                                                && 0 <= i₁₇
                                                                && i₁₇ < i₃₃ + 1
                                                                 ==> i₁₇ < 200000))
                                                        && true
                                                        && (true
                                                           ==> true)))
                                                && (!(i₃₃ < 200000
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> true
                                                        && 0 <= 0
                                                        && 0 <= 200000
                                                        && (forall x₂₂: int ::
                                                              ((exists i₂₁: int ::
                                                                      x₂₂ == i₂₁
                                                                      && 0 <= i₂₁
                                                                      && i₂₁ < 0)
                                                                 ==> (exists i₂₁: int ::
                                                                          i₂₁ != 150000
                                                                          && i₂₁ < 200000
                                                                          && x₂₂ == i₂₁
                                                                          && 0 <= i₂₁
                                                                          && i₂₁ < 0
                                                                          && a3₃₀[x₂₂] == a2₃₂[i₂₁])
                                                                  || (exists i₂₁: int ::
                                                                          i₂₁ == 150000
                                                                          && i₂₁ < 200000
                                                                          && x₂₂ == i₂₁
                                                                          && 0 <= i₂₁
                                                                          && i₂₁ < 0
                                                                          && a3₃₀[x₂₂] == a1₂₈[i₂₁])))
                                                        && (forall x₂₂: int ::
                                                              (!((exists i₂₁: int ::
                                                                      x₂₂ == i₂₁
                                                                      && 0 <= i₂₁
                                                                      && i₂₁ < 0)
                                                              )
                                                                 ==> a3₃₀[x₂₂] == a3₃₀[x₂₂]))
                                                        && (forall i₂₁: int ::
                                                              (  i₂₁ <= i₂₁
                                                                && 0 <= i₂₁
                                                                && i₂₁ < 0
                                                                 ==> i₂₁ < 200000))
                                                        && (forall a3₃₄: [int]int, i₃₅: int ::
                                                              (  true
                                                                && 0 <= i₃₅
                                                                && i₃₅ <= 200000
                                                                && (forall x₂₂: int ::
                                                                      ((exists i₂₁: int ::
                                                                              x₂₂ == i₂₁
                                                                              && 0 <= i₂₁
                                                                              && i₂₁ < i₃₅)
                                                                         ==> (exists i₂₁: int ::
                                                                                  i₂₁ != 150000
                                                                                  && i₂₁ < 200000
                                                                                  && x₂₂ == i₂₁
                                                                                  && 0 <= i₂₁
                                                                                  && i₂₁ < i₃₅
                                                                                  && a3₃₄[x₂₂] == a2₃₂[i₂₁])
                                                                          || (exists i₂₁: int ::
                                                                                  i₂₁ == 150000
                                                                                  && i₂₁ < 200000
                                                                                  && x₂₂ == i₂₁
                                                                                  && 0 <= i₂₁
                                                                                  && i₂₁ < i₃₅
                                                                                  && a3₃₄[x₂₂] == a1₂₈[i₂₁])))
                                                                && (forall x₂₂: int ::
                                                                      (!((exists i₂₁: int ::
                                                                              x₂₂ == i₂₁
                                                                              && 0 <= i₂₁
                                                                              && i₂₁ < i₃₅)
                                                                      )
                                                                         ==> a3₃₄[x₂₂] == a3₃₀[x₂₂]))
                                                                && (forall i₂₁: int ::
                                                                      (  i₂₁ <= i₂₁
                                                                        && 0 <= i₂₁
                                                                        && i₂₁ < i₃₅
                                                                         ==> i₂₁ < 200000))
                                                                 ==> (i₃₅ < 200000
                                                                     ==> (i₃₅ != 150000
                                                                         ==> true
                                                                          && 0 <= i₃₅ + 1
                                                                          && i₃₅ + 1 <= 200000
                                                                          && (forall x₂₂: int ::
                                                                                ((exists i₂₁: int ::
                                                                                        x₂₂ == i₂₁
                                                                                        && 0 <= i₂₁
                                                                                        && i₂₁ < i₃₅ + 1)
                                                                                   ==> (exists i₂₁: int ::
                                                                                            i₂₁ != 150000
                                                                                            && i₂₁ < 200000
                                                                                            && x₂₂ == i₂₁
                                                                                            && 0 <= i₂₁
                                                                                            && i₂₁ < i₃₅ + 1
                                                                                            && a3₃₄[i₃₅ := a2₃₂[i₃₅]][x₂₂] == a2₃₂[i₂₁])
                                                                                    || (exists i₂₁: int ::
                                                                                            i₂₁ == 150000
                                                                                            && i₂₁ < 200000
                                                                                            && x₂₂ == i₂₁
                                                                                            && 0 <= i₂₁
                                                                                            && i₂₁ < i₃₅ + 1
                                                                                            && a3₃₄[i₃₅ := a2₃₂[i₃₅]][x₂₂] == a1₂₈[i₂₁])))
                                                                          && (forall x₂₂: int ::
                                                                                (!((exists i₂₁: int ::
                                                                                        x₂₂ == i₂₁
                                                                                        && 0 <= i₂₁
                                                                                        && i₂₁ < i₃₅ + 1)
                                                                                )
                                                                                   ==> a3₃₄[i₃₅ := a2₃₂[i₃₅]][x₂₂] == a3₃₀[x₂₂]))
                                                                          && (forall i₂₁: int ::
                                                                                (  i₂₁ <= i₂₁
                                                                                  && 0 <= i₂₁
                                                                                  && i₂₁ < i₃₅ + 1
                                                                                   ==> i₂₁ < 200000))
                                                                          && true
                                                                          && (true
                                                                             ==> true))
                                                                      && (!(i₃₅ != 150000
                                                                      )
                                                                         ==> true
                                                                          && 0 <= i₃₅ + 1
                                                                          && i₃₅ + 1 <= 200000
                                                                          && (forall x₂₂: int ::
                                                                                ((exists i₂₁: int ::
                                                                                        x₂₂ == i₂₁
                                                                                        && 0 <= i₂₁
                                                                                        && i₂₁ < i₃₅ + 1)
                                                                                   ==> (exists i₂₁: int ::
                                                                                            i₂₁ != 150000
                                                                                            && i₂₁ < 200000
                                                                                            && x₂₂ == i₂₁
                                                                                            && 0 <= i₂₁
                                                                                            && i₂₁ < i₃₅ + 1
                                                                                            && a3₃₄[i₃₅ := a1₂₈[i₃₅]][x₂₂] == a2₃₂[i₂₁])
                                                                                    || (exists i₂₁: int ::
                                                                                            i₂₁ == 150000
                                                                                            && i₂₁ < 200000
                                                                                            && x₂₂ == i₂₁
                                                                                            && 0 <= i₂₁
                                                                                            && i₂₁ < i₃₅ + 1
                                                                                            && a3₃₄[i₃₅ := a1₂₈[i₃₅]][x₂₂] == a1₂₈[i₂₁])))
                                                                          && (forall x₂₂: int ::
                                                                                (!((exists i₂₁: int ::
                                                                                        x₂₂ == i₂₁
                                                                                        && 0 <= i₂₁
                                                                                        && i₂₁ < i₃₅ + 1)
                                                                                )
                                                                                   ==> a3₃₄[i₃₅ := a1₂₈[i₃₅]][x₂₂] == a3₃₀[x₂₂]))
                                                                          && (forall i₂₁: int ::
                                                                                (  i₂₁ <= i₂₁
                                                                                  && 0 <= i₂₁
                                                                                  && i₂₁ < i₃₅ + 1
                                                                                   ==> i₂₁ < 200000))
                                                                          && true
                                                                          && (true
                                                                             ==> true)))
                                                                  && (!(i₃₅ < 200000
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true
                                                                          && 0 <= 0
                                                                          && 0 <= 200000
                                                                          && (forall x₂₆: int ::
                                                                                (  x₂₆ <= x₂₆
                                                                                  && 0 <= x₂₆
                                                                                  && x₂₆ < 0
                                                                                   ==> x₂₆ < 200000))
                                                                          && (forall x₃₆: int ::
                                                                                (  true
                                                                                  && 0 <= x₃₆
                                                                                  && x₃₆ <= 200000
                                                                                  && (forall x₂₆: int ::
                                                                                        (  x₂₆ <= x₂₆
                                                                                          && 0 <= x₂₆
                                                                                          && x₂₆ < x₃₆
                                                                                           ==> x₂₆ < 200000))
                                                                                   ==> (x₃₆ < 200000
                                                                                       ==> a1₂₈[x₃₆] == a3₃₄[x₃₆]
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 0 <= x₃₆ + 1
                                                                                            && x₃₆ + 1 <= 200000
                                                                                            && (forall x₂₆: int ::
                                                                                                  (  x₂₆ <= x₂₆
                                                                                                    && 0 <= x₂₆
                                                                                                    && x₂₆ < x₃₆ + 1
                                                                                                     ==> x₂₆ < 200000))
                                                                                            && true
                                                                                            && (true
                                                                                               ==> true)))
                                                                                    && (!(x₃₆ < 200000
                                                                                    )
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true)))))))))))))))))));


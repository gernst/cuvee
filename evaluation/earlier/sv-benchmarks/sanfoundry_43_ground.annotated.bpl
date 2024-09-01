data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall src: [int]int, dst: [int]int ::
        true
        && 0 <= 0
        && 0 <= 100000
        && (forall x₃: int ::
              ((exists i₂: int ::
                      x₃ == i₂
                      && 0 <= i₂
                      && i₂ < 0)
                 ==> (exists i₂: int ::
                        i₂ < 100000
                        && x₃ == i₂
                        && 0 <= i₂
                        && i₂ < 0
                        && dst[x₃] == 1 + src[i₂])))
        && (forall x₃: int ::
              (!((exists i₂: int ::
                      x₃ == i₂
                      && 0 <= i₂
                      && i₂ < 0)
              )
                 ==> dst[x₃] == dst[x₃]))
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < 0
                 ==> i₂ < 100000))
        && (forall dst₁₉: [int]int, i₂₀: int ::
              (  true
                && 0 <= i₂₀
                && i₂₀ <= 100000
                && (forall x₃: int ::
                      ((exists i₂: int ::
                              x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₂₀)
                         ==> (exists i₂: int ::
                                i₂ < 100000
                                && x₃ == i₂
                                && 0 <= i₂
                                && i₂ < i₂₀
                                && dst₁₉[x₃] == 1 + src[i₂])))
                && (forall x₃: int ::
                      (!((exists i₂: int ::
                              x₃ == i₂
                              && 0 <= i₂
                              && i₂ < i₂₀)
                      )
                         ==> dst₁₉[x₃] == dst[x₃]))
                && (forall i₂: int ::
                      (  i₂ <= i₂
                        && 0 <= i₂
                        && i₂ < i₂₀
                         ==> i₂ < 100000))
                 ==> (i₂₀ < 100000
                     ==> true
                      && 0 <= i₂₀ + 1
                      && i₂₀ + 1 <= 100000
                      && (forall x₃: int ::
                            ((exists i₂: int ::
                                    x₃ == i₂
                                    && 0 <= i₂
                                    && i₂ < i₂₀ + 1)
                               ==> (exists i₂: int ::
                                      i₂ < 100000
                                      && x₃ == i₂
                                      && 0 <= i₂
                                      && i₂ < i₂₀ + 1
                                      && dst₁₉[i₂₀ := src[i₂₀] + 1][x₃] == 1 + src[i₂])))
                      && (forall x₃: int ::
                            (!((exists i₂: int ::
                                    x₃ == i₂
                                    && 0 <= i₂
                                    && i₂ < i₂₀ + 1)
                            )
                               ==> dst₁₉[i₂₀ := src[i₂₀] + 1][x₃] == dst[x₃]))
                      && (forall i₂: int ::
                            (  i₂ <= i₂
                              && 0 <= i₂
                              && i₂ < i₂₀ + 1
                               ==> i₂ < 100000))
                      && true
                      && (true
                         ==> true))
                  && (!(i₂₀ < 100000
                  )
                     ==> true
                      && (true
                         ==> true)))));

goal (forall src: [int]int ::
      (forall dst: [int]int ::
              true
              && 0 <= 0
              && 0 <= 100000
              && (forall x₁₀: int ::
                    ((exists i₉: int ::
                            x₁₀ == i₉
                            && 0 <= i₉
                            && i₉ < 0)
                       ==> (exists __VERIFIER_nondet_int₂₈: int, i₉: int ::
                              i₉ < 100000
                              && x₁₀ == i₉
                              && 0 <= i₉
                              && i₉ < 0
                              && src[x₁₀] == __VERIFIER_nondet_int₂₈)))
              && (forall x₁₀: int ::
                    (!((exists i₉: int ::
                            x₁₀ == i₉
                            && 0 <= i₉
                            && i₉ < 0)
                    )
                       ==> src[x₁₀] == src[x₁₀]))
              && (forall i₉: int ::
                    (  i₉ <= i₉
                      && 0 <= i₉
                      && i₉ < 0
                       ==> i₉ < 100000))
              && (forall src₂₃: [int]int, i₂₄: int ::
                    (  true
                      && 0 <= i₂₄
                      && i₂₄ <= 100000
                      && (forall x₁₀: int ::
                            ((exists i₉: int ::
                                    x₁₀ == i₉
                                    && 0 <= i₉
                                    && i₉ < i₂₄)
                               ==> (exists __VERIFIER_nondet_int₂₈: int, i₉: int ::
                                      i₉ < 100000
                                      && x₁₀ == i₉
                                      && 0 <= i₉
                                      && i₉ < i₂₄
                                      && src₂₃[x₁₀] == __VERIFIER_nondet_int₂₈)))
                      && (forall x₁₀: int ::
                            (!((exists i₉: int ::
                                    x₁₀ == i₉
                                    && 0 <= i₉
                                    && i₉ < i₂₄)
                            )
                               ==> src₂₃[x₁₀] == src[x₁₀]))
                      && (forall i₉: int ::
                            (  i₉ <= i₉
                              && 0 <= i₉
                              && i₉ < i₂₄
                               ==> i₉ < 100000))
                       ==> (i₂₄ < 100000
                           ==> (forall __VERIFIER_nondet_int₂: int ::
                                  true
                                  && 0 <= i₂₄ + 1
                                  && i₂₄ + 1 <= 100000
                                  && (forall x₁₀: int ::
                                        ((exists i₉: int ::
                                                x₁₀ == i₉
                                                && 0 <= i₉
                                                && i₉ < i₂₄ + 1)
                                           ==> (exists __VERIFIER_nondet_int₂₈: int, i₉: int ::
                                                  i₉ < 100000
                                                  && x₁₀ == i₉
                                                  && 0 <= i₉
                                                  && i₉ < i₂₄ + 1
                                                  && src₂₃[i₂₄ := __VERIFIER_nondet_int₂][x₁₀] == __VERIFIER_nondet_int₂₈)))
                                  && (forall x₁₀: int ::
                                        (!((exists i₉: int ::
                                                x₁₀ == i₉
                                                && 0 <= i₉
                                                && i₉ < i₂₄ + 1)
                                        )
                                           ==> src₂₃[i₂₄ := __VERIFIER_nondet_int₂][x₁₀] == src[x₁₀]))
                                  && (forall i₉: int ::
                                        (  i₉ <= i₉
                                          && 0 <= i₉
                                          && i₉ < i₂₄ + 1
                                           ==> i₉ < 100000))
                                  && true
                                  && (true
                                     ==> true)))
                        && (!(i₂₄ < 100000
                        )
                           ==> true
                            && (true
                               ==> true
                                && (true
                                   ==> true
                                    && 0 <= 0
                                    && 0 <= 100000
                                    && (forall x₃: int ::
                                          ((exists i₂: int ::
                                                  x₃ == i₂
                                                  && 0 <= i₂
                                                  && i₂ < 0)
                                             ==> (exists i₂: int ::
                                                    i₂ < 100000
                                                    && x₃ == i₂
                                                    && 0 <= i₂
                                                    && i₂ < 0
                                                    && dst[x₃] == 1 + src₂₃[i₂])))
                                    && (forall x₃: int ::
                                          (!((exists i₂: int ::
                                                  x₃ == i₂
                                                  && 0 <= i₂
                                                  && i₂ < 0)
                                          )
                                             ==> dst[x₃] == dst[x₃]))
                                    && (forall i₂: int ::
                                          (  i₂ <= i₂
                                            && 0 <= i₂
                                            && i₂ < 0
                                             ==> i₂ < 100000))
                                    && (forall dst₂₉: [int]int, i₃₀: int ::
                                          (  true
                                            && 0 <= i₃₀
                                            && i₃₀ <= 100000
                                            && (forall x₃: int ::
                                                  ((exists i₂: int ::
                                                          x₃ == i₂
                                                          && 0 <= i₂
                                                          && i₂ < i₃₀)
                                                     ==> (exists i₂: int ::
                                                            i₂ < 100000
                                                            && x₃ == i₂
                                                            && 0 <= i₂
                                                            && i₂ < i₃₀
                                                            && dst₂₉[x₃] == 1 + src₂₃[i₂])))
                                            && (forall x₃: int ::
                                                  (!((exists i₂: int ::
                                                          x₃ == i₂
                                                          && 0 <= i₂
                                                          && i₂ < i₃₀)
                                                  )
                                                     ==> dst₂₉[x₃] == dst[x₃]))
                                            && (forall i₂: int ::
                                                  (  i₂ <= i₂
                                                    && 0 <= i₂
                                                    && i₂ < i₃₀
                                                     ==> i₂ < 100000))
                                             ==> (i₃₀ < 100000
                                                 ==> true
                                                  && 0 <= i₃₀ + 1
                                                  && i₃₀ + 1 <= 100000
                                                  && (forall x₃: int ::
                                                        ((exists i₂: int ::
                                                                x₃ == i₂
                                                                && 0 <= i₂
                                                                && i₂ < i₃₀ + 1)
                                                           ==> (exists i₂: int ::
                                                                  i₂ < 100000
                                                                  && x₃ == i₂
                                                                  && 0 <= i₂
                                                                  && i₂ < i₃₀ + 1
                                                                  && dst₂₉[i₃₀ := src₂₃[i₃₀] + 1][x₃] == 1 + src₂₃[i₂])))
                                                  && (forall x₃: int ::
                                                        (!((exists i₂: int ::
                                                                x₃ == i₂
                                                                && 0 <= i₂
                                                                && i₂ < i₃₀ + 1)
                                                        )
                                                           ==> dst₂₉[i₃₀ := src₂₃[i₃₀] + 1][x₃] == dst[x₃]))
                                                  && (forall i₂: int ::
                                                        (  i₂ <= i₂
                                                          && 0 <= i₂
                                                          && i₂ < i₃₀ + 1
                                                           ==> i₂ < 100000))
                                                  && true
                                                  && (true
                                                     ==> true))
                                              && (!(i₃₀ < 100000
                                              )
                                                 ==> true
                                                  && (true
                                                     ==> true
                                                      && 0 <= 0
                                                      && 0 <= 100000
                                                      && (forall x₁₆: int ::
                                                            ((exists x₁₅: int ::
                                                                    x₁₆ == x₁₅
                                                                    && 0 <= x₁₅
                                                                    && x₁₅ < 0)
                                                               ==> (exists x₁₅: int ::
                                                                      x₁₅ < 100000
                                                                      && x₁₆ == x₁₅
                                                                      && 0 <= x₁₅
                                                                      && x₁₅ < 0
                                                                      && src₂₃[x₁₆] == -1 + dst[x₁₅])))
                                                      && (forall x₁₆: int ::
                                                            (!((exists x₁₅: int ::
                                                                    x₁₆ == x₁₅
                                                                    && 0 <= x₁₅
                                                                    && x₁₅ < 0)
                                                            )
                                                               ==> src₂₃[x₁₆] == src₂₃[x₁₆]))
                                                      && (forall x₁₅: int ::
                                                            (  x₁₅ <= x₁₅
                                                              && 0 <= x₁₅
                                                              && x₁₅ < 0
                                                               ==> x₁₅ < 100000))
                                                      && (forall src₃₁: [int]int, x₃₂: int ::
                                                            (  true
                                                              && 0 <= x₃₂
                                                              && x₃₂ <= 100000
                                                              && (forall x₁₆: int ::
                                                                    ((exists x₁₅: int ::
                                                                            x₁₆ == x₁₅
                                                                            && 0 <= x₁₅
                                                                            && x₁₅ < x₃₂)
                                                                       ==> (exists x₁₅: int ::
                                                                              x₁₅ < 100000
                                                                              && x₁₆ == x₁₅
                                                                              && 0 <= x₁₅
                                                                              && x₁₅ < x₃₂
                                                                              && src₃₁[x₁₆] == -1 + dst[x₁₅])))
                                                              && (forall x₁₆: int ::
                                                                    (!((exists x₁₅: int ::
                                                                            x₁₆ == x₁₅
                                                                            && 0 <= x₁₅
                                                                            && x₁₅ < x₃₂)
                                                                    )
                                                                       ==> src₃₁[x₁₆] == src₂₃[x₁₆]))
                                                              && (forall x₁₅: int ::
                                                                    (  x₁₅ <= x₁₅
                                                                      && 0 <= x₁₅
                                                                      && x₁₅ < x₃₂
                                                                       ==> x₁₅ < 100000))
                                                               ==> (x₃₂ < 100000
                                                                   ==> true
                                                                    && 0 <= x₃₂ + 1
                                                                    && x₃₂ + 1 <= 100000
                                                                    && (forall x₁₆: int ::
                                                                          ((exists x₁₅: int ::
                                                                                  x₁₆ == x₁₅
                                                                                  && 0 <= x₁₅
                                                                                  && x₁₅ < x₃₂ + 1)
                                                                             ==> (exists x₁₅: int ::
                                                                                    x₁₅ < 100000
                                                                                    && x₁₆ == x₁₅
                                                                                    && 0 <= x₁₅
                                                                                    && x₁₅ < x₃₂ + 1
                                                                                    && src₃₁[x₃₂ := dst[x₃₂] - 1][x₁₆] == -1 + dst[x₁₅])))
                                                                    && (forall x₁₆: int ::
                                                                          (!((exists x₁₅: int ::
                                                                                  x₁₆ == x₁₅
                                                                                  && 0 <= x₁₅
                                                                                  && x₁₅ < x₃₂ + 1)
                                                                          )
                                                                             ==> src₃₁[x₃₂ := dst[x₃₂] - 1][x₁₆] == src₂₃[x₁₆]))
                                                                    && (forall x₁₅: int ::
                                                                          (  x₁₅ <= x₁₅
                                                                            && 0 <= x₁₅
                                                                            && x₁₅ < x₃₂ + 1
                                                                             ==> x₁₅ < 100000))
                                                                    && true
                                                                    && (true
                                                                       ==> true))
                                                                && (!(x₃₂ < 100000
                                                                )
                                                                   ==> true
                                                                    && (true
                                                                       ==> true)))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall src: [int]int, dst: [int]int ::
        true
        && 0 <= 0
        && 0 <= 100000
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < 0
                 ==> i₂ < 100000
                  && !(  dst[i₂] != src[i₂]
                    && i₂ < 100000
                  )))
        && (forall i₂₁: int ::
              (  true
                && 0 <= i₂₁
                && i₂₁ <= 100000
                && (forall i₂: int ::
                      (  i₂ <= i₂
                        && 0 <= i₂
                        && i₂ < i₂₁
                         ==> i₂ < 100000
                          && !(  dst[i₂] != src[i₂]
                            && i₂ < 100000
                          )))
                 ==> (i₂₁ < 100000
                     ==> (dst[i₂₁] != src[i₂₁]
                         ==> ((true
                           ==> true)
                           ==> true))
                      && (!(dst[i₂₁] != src[i₂₁]
                      )
                         ==> true
                          && 0 <= i₂₁ + 1
                          && i₂₁ + 1 <= 100000
                          && (forall i₂: int ::
                                (  i₂ <= i₂
                                  && 0 <= i₂
                                  && i₂ < i₂₁ + 1
                                   ==> i₂ < 100000
                                    && !(  dst[i₂] != src[i₂]
                                      && i₂ < 100000
                                    )))
                          && true
                          && (true
                             ==> true)))
                  && (!(i₂₁ < 100000
                  )
                     ==> true
                      && (true
                         ==> true)))));

goal (forall a: [int]int ::
      (forall b: [int]int ::
              true
              && 0 <= 0
              && 0 <= 100000
              && (forall x₁₀: int ::
                    ((exists i₉: int ::
                            x₁₀ == i₉
                            && 0 <= i₉
                            && i₉ < 0)
                       ==> (exists __VERIFIER_nondet_int₁₇: int, i₉: int ::
                              i₉ < 100000
                              && x₁₀ == i₉
                              && 0 <= i₉
                              && i₉ < 0
                              && a[x₁₀] == __VERIFIER_nondet_int₁₇)))
              && (forall x₁₀: int ::
                    (!((exists i₉: int ::
                            x₁₀ == i₉
                            && 0 <= i₉
                            && i₉ < 0)
                    )
                       ==> a[x₁₀] == a[x₁₀]))
              && (forall x₁₁: int ::
                    ((exists i₉: int ::
                            x₁₁ == i₉
                            && 0 <= i₉
                            && i₉ < 0)
                       ==> (exists __VERIFIER_nondet_int₂₈: int, i₉: int ::
                              i₉ < 100000
                              && x₁₁ == i₉
                              && 0 <= i₉
                              && i₉ < 0
                              && b[x₁₁] == __VERIFIER_nondet_int₂₈)))
              && (forall x₁₁: int ::
                    (!((exists i₉: int ::
                            x₁₁ == i₉
                            && 0 <= i₉
                            && i₉ < 0)
                    )
                       ==> b[x₁₁] == b[x₁₁]))
              && (forall i₉: int ::
                    (  i₉ <= i₉
                      && 0 <= i₉
                      && i₉ < 0
                       ==> i₉ < 100000))
              && (forall a₂₄: [int]int, b₂₅: [int]int, i₂₆: int ::
                    (  true
                      && 0 <= i₂₆
                      && i₂₆ <= 100000
                      && (forall x₁₀: int ::
                            ((exists i₉: int ::
                                    x₁₀ == i₉
                                    && 0 <= i₉
                                    && i₉ < i₂₆)
                               ==> (exists __VERIFIER_nondet_int₁₇: int, i₉: int ::
                                      i₉ < 100000
                                      && x₁₀ == i₉
                                      && 0 <= i₉
                                      && i₉ < i₂₆
                                      && a₂₄[x₁₀] == __VERIFIER_nondet_int₁₇)))
                      && (forall x₁₀: int ::
                            (!((exists i₉: int ::
                                    x₁₀ == i₉
                                    && 0 <= i₉
                                    && i₉ < i₂₆)
                            )
                               ==> a₂₄[x₁₀] == a[x₁₀]))
                      && (forall x₁₁: int ::
                            ((exists i₉: int ::
                                    x₁₁ == i₉
                                    && 0 <= i₉
                                    && i₉ < i₂₆)
                               ==> (exists __VERIFIER_nondet_int₂₈: int, i₉: int ::
                                      i₉ < 100000
                                      && x₁₁ == i₉
                                      && 0 <= i₉
                                      && i₉ < i₂₆
                                      && b₂₅[x₁₁] == __VERIFIER_nondet_int₂₈)))
                      && (forall x₁₁: int ::
                            (!((exists i₉: int ::
                                    x₁₁ == i₉
                                    && 0 <= i₉
                                    && i₉ < i₂₆)
                            )
                               ==> b₂₅[x₁₁] == b[x₁₁]))
                      && (forall i₉: int ::
                            (  i₉ <= i₉
                              && 0 <= i₉
                              && i₉ < i₂₆
                               ==> i₉ < 100000))
                       ==> (i₂₆ < 100000
                           ==> (forall __VERIFIER_nondet_int₁: int ::
                                (forall __VERIFIER_nondet_int₂: int ::
                                        true
                                        && 0 <= i₂₆ + 1
                                        && i₂₆ + 1 <= 100000
                                        && (forall x₁₀: int ::
                                              ((exists i₉: int ::
                                                      x₁₀ == i₉
                                                      && 0 <= i₉
                                                      && i₉ < i₂₆ + 1)
                                                 ==> (exists __VERIFIER_nondet_int₁₇: int, i₉: int ::
                                                        i₉ < 100000
                                                        && x₁₀ == i₉
                                                        && 0 <= i₉
                                                        && i₉ < i₂₆ + 1
                                                        && a₂₄[i₂₆ := __VERIFIER_nondet_int₁][x₁₀] == __VERIFIER_nondet_int₁₇)))
                                        && (forall x₁₀: int ::
                                              (!((exists i₉: int ::
                                                      x₁₀ == i₉
                                                      && 0 <= i₉
                                                      && i₉ < i₂₆ + 1)
                                              )
                                                 ==> a₂₄[i₂₆ := __VERIFIER_nondet_int₁][x₁₀] == a[x₁₀]))
                                        && (forall x₁₁: int ::
                                              ((exists i₉: int ::
                                                      x₁₁ == i₉
                                                      && 0 <= i₉
                                                      && i₉ < i₂₆ + 1)
                                                 ==> (exists __VERIFIER_nondet_int₂₈: int, i₉: int ::
                                                        i₉ < 100000
                                                        && x₁₁ == i₉
                                                        && 0 <= i₉
                                                        && i₉ < i₂₆ + 1
                                                        && b₂₅[i₂₆ := __VERIFIER_nondet_int₂][x₁₁] == __VERIFIER_nondet_int₂₈)))
                                        && (forall x₁₁: int ::
                                              (!((exists i₉: int ::
                                                      x₁₁ == i₉
                                                      && 0 <= i₉
                                                      && i₉ < i₂₆ + 1)
                                              )
                                                 ==> b₂₅[i₂₆ := __VERIFIER_nondet_int₂][x₁₁] == b[x₁₁]))
                                        && (forall i₉: int ::
                                              (  i₉ <= i₉
                                                && 0 <= i₉
                                                && i₉ < i₂₆ + 1
                                                 ==> i₉ < 100000))
                                        && true
                                        && (true
                                           ==> true))))
                        && (!(i₂₆ < 100000
                        )
                           ==> true
                            && (true
                               ==> true
                                && (true
                                   ==> true
                                    && 0 <= 0
                                    && 0 <= 100000
                                    && (forall i₂: int ::
                                          (  i₂ <= i₂
                                            && 0 <= i₂
                                            && i₂ < 0
                                             ==> i₂ < 100000
                                              && !(  b₂₅[i₂] != a₂₄[i₂]
                                                && i₂ < 100000
                                              )))
                                    && (forall i₃₀: int ::
                                          (  true
                                            && 0 <= i₃₀
                                            && i₃₀ <= 100000
                                            && (forall i₂: int ::
                                                  (  i₂ <= i₂
                                                    && 0 <= i₂
                                                    && i₂ < i₃₀
                                                     ==> i₂ < 100000
                                                      && !(  b₂₅[i₂] != a₂₄[i₂]
                                                        && i₂ < 100000
                                                      )))
                                             ==> (i₃₀ < 100000
                                                 ==> (b₂₅[i₃₀] != a₂₄[i₃₀]
                                                     ==> ((true
                                                       ==> true)
                                                       ==> (1 == 0
                                                           ==> true
                                                            && 0 <= 0
                                                            && 0 <= 100000
                                                            && (forall x₁₈: int ::
                                                                  (  x₁₈ <= x₁₈
                                                                    && 0 <= x₁₈
                                                                    && x₁₈ < 0
                                                                     ==> x₁₈ < 100000))
                                                            && (forall x₃₃: int ::
                                                                  (  true
                                                                    && 0 <= x₃₃
                                                                    && x₃₃ <= 100000
                                                                    && (forall x₁₈: int ::
                                                                          (  x₁₈ <= x₁₈
                                                                            && 0 <= x₁₈
                                                                            && x₁₈ < x₃₃
                                                                             ==> x₁₈ < 100000))
                                                                     ==> (x₃₃ < 100000
                                                                         ==> a₂₄[x₃₃] == b₂₅[x₃₃]
                                                                          && (true
                                                                             ==> true
                                                                              && 0 <= x₃₃ + 1
                                                                              && x₃₃ + 1 <= 100000
                                                                              && (forall x₁₈: int ::
                                                                                    (  x₁₈ <= x₁₈
                                                                                      && 0 <= x₁₈
                                                                                      && x₁₈ < x₃₃ + 1
                                                                                       ==> x₁₈ < 100000))
                                                                              && true
                                                                              && (true
                                                                                 ==> true)))
                                                                      && (!(x₃₃ < 100000
                                                                      )
                                                                         ==> true
                                                                          && (true
                                                                             ==> true)))))
                                                        && (1 != 0
                                                           ==> true)))
                                                  && (!(b₂₅[i₃₀] != a₂₄[i₃₀]
                                                  )
                                                     ==> true
                                                      && 0 <= i₃₀ + 1
                                                      && i₃₀ + 1 <= 100000
                                                      && (forall i₂: int ::
                                                            (  i₂ <= i₂
                                                              && 0 <= i₂
                                                              && i₂ < i₃₀ + 1
                                                               ==> i₂ < 100000
                                                                && !(  b₂₅[i₂] != a₂₄[i₂]
                                                                  && i₂ < 100000
                                                                )))
                                                      && true
                                                      && (true
                                                         ==> true)))
                                              && (!(i₃₀ < 100000
                                              )
                                                 ==> true
                                                  && (true
                                                     ==> (0 == 0
                                                         ==> true
                                                          && 0 <= 0
                                                          && 0 <= 100000
                                                          && (forall x₁₈: int ::
                                                                (  x₁₈ <= x₁₈
                                                                  && 0 <= x₁₈
                                                                  && x₁₈ < 0
                                                                   ==> x₁₈ < 100000))
                                                          && (forall x₃₁: int ::
                                                                (  true
                                                                  && 0 <= x₃₁
                                                                  && x₃₁ <= 100000
                                                                  && (forall x₁₈: int ::
                                                                        (  x₁₈ <= x₁₈
                                                                          && 0 <= x₁₈
                                                                          && x₁₈ < x₃₁
                                                                           ==> x₁₈ < 100000))
                                                                   ==> (x₃₁ < 100000
                                                                       ==> a₂₄[x₃₁] == b₂₅[x₃₁]
                                                                        && (true
                                                                           ==> true
                                                                            && 0 <= x₃₁ + 1
                                                                            && x₃₁ + 1 <= 100000
                                                                            && (forall x₁₈: int ::
                                                                                  (  x₁₈ <= x₁₈
                                                                                    && 0 <= x₁₈
                                                                                    && x₁₈ < x₃₁ + 1
                                                                                     ==> x₁₈ < 100000))
                                                                            && true
                                                                            && (true
                                                                               ==> true)))
                                                                    && (!(x₃₁ < 100000
                                                                    )
                                                                       ==> true
                                                                        && (true
                                                                           ==> true)))))
                                                      && (0 != 0
                                                         ==> true))))))))))));


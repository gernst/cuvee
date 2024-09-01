data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
      (forall b: [int]int ::
            (forall __VERIFIER_nondet_int₁: int ::
                    true
                    && 0 <= 0
                    && 0 <= 100000
                    && (forall x₆: int ::
                          ((exists i₅: int ::
                                  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                             ==> (exists i₅: int ::
                                    i₅ < 100000
                                    && x₆ == i₅
                                    && 0 <= i₅
                                    && i₅ < 0
                                    && a[x₆] == 42)))
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
                             ==> i₅ < 100000))
                    && (forall a₂₀: [int]int, i₂₁: int ::
                          (  true
                            && 0 <= i₂₁
                            && i₂₁ <= 100000
                            && (forall x₆: int ::
                                  ((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₁)
                                     ==> (exists i₅: int ::
                                            i₅ < 100000
                                            && x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₂₁
                                            && a₂₀[x₆] == 42)))
                            && (forall x₆: int ::
                                  (!((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₁)
                                  )
                                     ==> a₂₀[x₆] == a[x₆]))
                            && (forall i₅: int ::
                                  (  i₅ <= i₅
                                    && 0 <= i₅
                                    && i₅ < i₂₁
                                     ==> i₅ < 100000))
                             ==> (i₂₁ < 100000
                                 ==> true
                                  && 0 <= i₂₁ + 1
                                  && i₂₁ + 1 <= 100000
                                  && (forall x₆: int ::
                                        ((exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₁ + 1)
                                           ==> (exists i₅: int ::
                                                  i₅ < 100000
                                                  && x₆ == i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₂₁ + 1
                                                  && a₂₀[i₂₁ := 42][x₆] == 42)))
                                  && (forall x₆: int ::
                                        (!((exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₁ + 1)
                                        )
                                           ==> a₂₀[i₂₁ := 42][x₆] == a[x₆]))
                                  && (forall i₅: int ::
                                        (  i₅ <= i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₁ + 1
                                           ==> i₅ < 100000))
                                  && true
                                  && (true
                                     ==> true))
                              && (!(i₂₁ < 100000
                              )
                                 ==> true
                                  && (true
                                     ==> true
                                      && 0 <= 0
                                      && 0 <= 100000
                                      && (forall x₁₀: int ::
                                            ((exists i₉: int ::
                                                    x₁₀ == i₉
                                                    && 0 <= i₉
                                                    && i₉ < 0)
                                               ==> (exists i₉: int ::
                                                      i₉ < 100000
                                                      && x₁₀ == i₉
                                                      && 0 <= i₉
                                                      && i₉ < 0
                                                      && b[x₁₀] == a₂₀[i₉])))
                                      && (forall x₁₀: int ::
                                            (!((exists i₉: int ::
                                                    x₁₀ == i₉
                                                    && 0 <= i₉
                                                    && i₉ < 0)
                                            )
                                               ==> b[x₁₀] == b[x₁₀]))
                                      && (forall i₉: int ::
                                            (  i₉ <= i₉
                                              && 0 <= i₉
                                              && i₉ < 0
                                               ==> i₉ < 100000))
                                      && (forall b₂₂: [int]int, i₂₃: int ::
                                            (  true
                                              && 0 <= i₂₃
                                              && i₂₃ <= 100000
                                              && (forall x₁₀: int ::
                                                    ((exists i₉: int ::
                                                            x₁₀ == i₉
                                                            && 0 <= i₉
                                                            && i₉ < i₂₃)
                                                       ==> (exists i₉: int ::
                                                              i₉ < 100000
                                                              && x₁₀ == i₉
                                                              && 0 <= i₉
                                                              && i₉ < i₂₃
                                                              && b₂₂[x₁₀] == a₂₀[i₉])))
                                              && (forall x₁₀: int ::
                                                    (!((exists i₉: int ::
                                                            x₁₀ == i₉
                                                            && 0 <= i₉
                                                            && i₉ < i₂₃)
                                                    )
                                                       ==> b₂₂[x₁₀] == b[x₁₀]))
                                              && (forall i₉: int ::
                                                    (  i₉ <= i₉
                                                      && 0 <= i₉
                                                      && i₉ < i₂₃
                                                       ==> i₉ < 100000))
                                               ==> (i₂₃ < 100000
                                                   ==> true
                                                    && 0 <= i₂₃ + 1
                                                    && i₂₃ + 1 <= 100000
                                                    && (forall x₁₀: int ::
                                                          ((exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₂₃ + 1)
                                                             ==> (exists i₉: int ::
                                                                    i₉ < 100000
                                                                    && x₁₀ == i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₂₃ + 1
                                                                    && b₂₂[i₂₃ := a₂₀[i₂₃]][x₁₀] == a₂₀[i₉])))
                                                    && (forall x₁₀: int ::
                                                          (!((exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₂₃ + 1)
                                                          )
                                                             ==> b₂₂[i₂₃ := a₂₀[i₂₃]][x₁₀] == b[x₁₀]))
                                                    && (forall i₉: int ::
                                                          (  i₉ <= i₉
                                                            && 0 <= i₉
                                                            && i₉ < i₂₃ + 1
                                                             ==> i₉ < 100000))
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
                                                        && (forall x₁₄: int ::
                                                              ((exists i₁₃: int ::
                                                                      x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < 0)
                                                                 ==> (exists i₁₃: int ::
                                                                        i₁₃ < 100000
                                                                        && x₁₄ == i₁₃
                                                                        && 0 <= i₁₃
                                                                        && i₁₃ < 0
                                                                        && b₂₂[x₁₄] == __VERIFIER_nondet_int₁ + b₂₂[i₁₃])))
                                                        && (forall x₁₄: int ::
                                                              (!((exists i₁₃: int ::
                                                                      x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < 0)
                                                              )
                                                                 ==> b₂₂[x₁₄] == b₂₂[x₁₄]))
                                                        && (forall i₁₃: int ::
                                                              (  i₁₃ <= i₁₃
                                                                && 0 <= i₁₃
                                                                && i₁₃ < 0
                                                                 ==> i₁₃ < 100000))
                                                        && (forall b₂₄: [int]int, i₂₅: int ::
                                                              (  true
                                                                && 0 <= i₂₅
                                                                && i₂₅ <= 100000
                                                                && (forall x₁₄: int ::
                                                                      ((exists i₁₃: int ::
                                                                              x₁₄ == i₁₃
                                                                              && 0 <= i₁₃
                                                                              && i₁₃ < i₂₅)
                                                                         ==> (exists i₁₃: int ::
                                                                                i₁₃ < 100000
                                                                                && x₁₄ == i₁₃
                                                                                && 0 <= i₁₃
                                                                                && i₁₃ < i₂₅
                                                                                && b₂₄[x₁₄] == __VERIFIER_nondet_int₁ + b₂₂[i₁₃])))
                                                                && (forall x₁₄: int ::
                                                                      (!((exists i₁₃: int ::
                                                                              x₁₄ == i₁₃
                                                                              && 0 <= i₁₃
                                                                              && i₁₃ < i₂₅)
                                                                      )
                                                                         ==> b₂₄[x₁₄] == b₂₂[x₁₄]))
                                                                && (forall i₁₃: int ::
                                                                      (  i₁₃ <= i₁₃
                                                                        && 0 <= i₁₃
                                                                        && i₁₃ < i₂₅
                                                                         ==> i₁₃ < 100000))
                                                                 ==> (i₂₅ < 100000
                                                                     ==> true
                                                                      && 0 <= i₂₅ + 1
                                                                      && i₂₅ + 1 <= 100000
                                                                      && (forall x₁₄: int ::
                                                                            ((exists i₁₃: int ::
                                                                                    x₁₄ == i₁₃
                                                                                    && 0 <= i₁₃
                                                                                    && i₁₃ < i₂₅ + 1)
                                                                               ==> (exists i₁₃: int ::
                                                                                      i₁₃ < 100000
                                                                                      && x₁₄ == i₁₃
                                                                                      && 0 <= i₁₃
                                                                                      && i₁₃ < i₂₅ + 1
                                                                                      && b₂₄[i₂₅ := b₂₄[i₂₅] + __VERIFIER_nondet_int₁][x₁₄] == __VERIFIER_nondet_int₁ + b₂₂[i₁₃])))
                                                                      && (forall x₁₄: int ::
                                                                            (!((exists i₁₃: int ::
                                                                                    x₁₄ == i₁₃
                                                                                    && 0 <= i₁₃
                                                                                    && i₁₃ < i₂₅ + 1)
                                                                            )
                                                                               ==> b₂₄[i₂₅ := b₂₄[i₂₅] + __VERIFIER_nondet_int₁][x₁₄] == b₂₂[x₁₄]))
                                                                      && (forall i₁₃: int ::
                                                                            (  i₁₃ <= i₁₃
                                                                              && 0 <= i₁₃
                                                                              && i₁₃ < i₂₅ + 1
                                                                               ==> i₁₃ < 100000))
                                                                      && true
                                                                      && (true
                                                                         ==> true))
                                                                  && (!(i₂₅ < 100000
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true
                                                                          && 0 <= 0
                                                                          && 0 <= 100000
                                                                          && (forall x₁₈: int ::
                                                                                (  x₁₈ <= x₁₈
                                                                                  && 0 <= x₁₈
                                                                                  && x₁₈ < 0
                                                                                   ==> x₁₈ < 100000))
                                                                          && (forall x₂₆: int ::
                                                                                (  true
                                                                                  && 0 <= x₂₆
                                                                                  && x₂₆ <= 100000
                                                                                  && (forall x₁₈: int ::
                                                                                        (  x₁₈ <= x₁₈
                                                                                          && 0 <= x₁₈
                                                                                          && x₁₈ < x₂₆
                                                                                           ==> x₁₈ < 100000))
                                                                                   ==> (x₂₆ < 100000
                                                                                       ==> b₂₄[x₂₆] == 42 + __VERIFIER_nondet_int₁
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 0 <= x₂₆ + 1
                                                                                            && x₂₆ + 1 <= 100000
                                                                                            && (forall x₁₈: int ::
                                                                                                  (  x₁₈ <= x₁₈
                                                                                                    && 0 <= x₁₈
                                                                                                    && x₁₈ < x₂₆ + 1
                                                                                                     ==> x₁₈ < 100000))
                                                                                            && true
                                                                                            && (true
                                                                                               ==> true)))
                                                                                    && (!(x₂₆ < 100000
                                                                                    )
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true)))))))))))))))))));


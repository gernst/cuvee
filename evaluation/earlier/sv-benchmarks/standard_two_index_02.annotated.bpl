data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
      (forall b: [int]int ::
              true
              && 0 <= 0
              && 0 <= 100000
              && (forall x₅: int ::
                    ((exists i₄: int ::
                            x₅ == i₄
                            && 0 <= i₄
                            && i₄ < 0)
                       ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                              i₄ < 100000
                              && x₅ == i₄
                              && 0 <= i₄
                              && i₄ < 0
                              && b[x₅] == __VERIFIER_nondet_int₁₃)))
              && (forall x₅: int ::
                    (!((exists i₄: int ::
                            x₅ == i₄
                            && 0 <= i₄
                            && i₄ < 0)
                    )
                       ==> b[x₅] == b[x₅]))
              && (forall i₄: int ::
                    (  i₄ <= i₄
                      && 0 <= i₄
                      && i₄ < 0
                       ==> i₄ < 100000))
              && (forall b₁₈: [int]int, i₁₉: int ::
                    (  true
                      && 0 <= i₁₉
                      && i₁₉ <= 100000
                      && (forall x₅: int ::
                            ((exists i₄: int ::
                                    x₅ == i₄
                                    && 0 <= i₄
                                    && i₄ < i₁₉)
                               ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                      i₄ < 100000
                                      && x₅ == i₄
                                      && 0 <= i₄
                                      && i₄ < i₁₉
                                      && b₁₈[x₅] == __VERIFIER_nondet_int₁₃)))
                      && (forall x₅: int ::
                            (!((exists i₄: int ::
                                    x₅ == i₄
                                    && 0 <= i₄
                                    && i₄ < i₁₉)
                            )
                               ==> b₁₈[x₅] == b[x₅]))
                      && (forall i₄: int ::
                            (  i₄ <= i₄
                              && 0 <= i₄
                              && i₄ < i₁₉
                               ==> i₄ < 100000))
                       ==> (i₁₉ < 100000
                           ==> (forall __VERIFIER_nondet_int₁: int ::
                                  true
                                  && 0 <= i₁₉ + 1
                                  && i₁₉ + 1 <= 100000
                                  && (forall x₅: int ::
                                        ((exists i₄: int ::
                                                x₅ == i₄
                                                && 0 <= i₄
                                                && i₄ < i₁₉ + 1)
                                           ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                                  i₄ < 100000
                                                  && x₅ == i₄
                                                  && 0 <= i₄
                                                  && i₄ < i₁₉ + 1
                                                  && b₁₈[i₁₉ := __VERIFIER_nondet_int₁][x₅] == __VERIFIER_nondet_int₁₃)))
                                  && (forall x₅: int ::
                                        (!((exists i₄: int ::
                                                x₅ == i₄
                                                && 0 <= i₄
                                                && i₄ < i₁₉ + 1)
                                        )
                                           ==> b₁₈[i₁₉ := __VERIFIER_nondet_int₁][x₅] == b[x₅]))
                                  && (forall i₄: int ::
                                        (  i₄ <= i₄
                                          && 0 <= i₄
                                          && i₄ < i₁₉ + 1
                                           ==> i₄ < 100000))
                                  && true
                                  && (true
                                     ==> true)))
                        && (!(i₁₉ < 100000
                        )
                           ==> true
                            && (true
                               ==> true
                                && 0 <= 0
                                && 1 <= 100000
                                && (forall x₁₀: int ::
                                      ((exists j₉: int ::
                                              x₁₀ == j₉
                                              && 0 <= j₉
                                              && j₉ < 0)
                                         ==> (exists i₈: int, j₉: int ::
                                                i₈ < 100000
                                                && x₁₀ == j₉
                                                && 0 <= j₉
                                                && j₉ < 0
                                                && a[x₁₀] == b₁₈[i₈])))
                                && (forall x₁₀: int ::
                                      (!((exists j₉: int ::
                                              x₁₀ == j₉
                                              && 0 <= j₉
                                              && j₉ < 0)
                                      )
                                         ==> a[x₁₀] == a[x₁₀]))
                                && (forall i₈: int, j₉: int ::
                                      (  j₉ <= j₉
                                        && 0 <= j₉
                                        && j₉ < 0
                                         ==> i₈ < 100000))
                                && (forall a₂₀: [int]int, i₂₁: int, j₂₂: int ::
                                      (  true
                                        && 0 <= j₂₂
                                        && i₂₁ <= 100000
                                        && (forall x₁₀: int ::
                                              ((exists j₉: int ::
                                                      x₁₀ == j₉
                                                      && 0 <= j₉
                                                      && j₉ < j₂₂)
                                                 ==> (exists i₈: int, j₉: int ::
                                                        i₈ < 100000
                                                        && x₁₀ == j₉
                                                        && 0 <= j₉
                                                        && j₉ < j₂₂
                                                        && a₂₀[x₁₀] == b₁₈[i₈])))
                                        && (forall x₁₀: int ::
                                              (!((exists j₉: int ::
                                                      x₁₀ == j₉
                                                      && 0 <= j₉
                                                      && j₉ < j₂₂)
                                              )
                                                 ==> a₂₀[x₁₀] == a[x₁₀]))
                                        && (forall i₈: int, j₉: int ::
                                              (  j₉ <= j₉
                                                && 0 <= j₉
                                                && j₉ < j₂₂
                                                 ==> i₈ < 100000))
                                         ==> (i₂₁ < 100000
                                             ==> true
                                              && 0 <= j₂₂ + 1
                                              && i₂₁ + 2 <= 100000
                                              && (forall x₁₀: int ::
                                                    ((exists j₉: int ::
                                                            x₁₀ == j₉
                                                            && 0 <= j₉
                                                            && j₉ < j₂₂ + 1)
                                                       ==> (exists i₈: int, j₉: int ::
                                                              i₈ < 100000
                                                              && x₁₀ == j₉
                                                              && 0 <= j₉
                                                              && j₉ < j₂₂ + 1
                                                              && a₂₀[j₂₂ := b₁₈[i₂₁]][x₁₀] == b₁₈[i₈])))
                                              && (forall x₁₀: int ::
                                                    (!((exists j₉: int ::
                                                            x₁₀ == j₉
                                                            && 0 <= j₉
                                                            && j₉ < j₂₂ + 1)
                                                    )
                                                       ==> a₂₀[j₂₂ := b₁₈[i₂₁]][x₁₀] == a[x₁₀]))
                                              && (forall i₈: int, j₉: int ::
                                                    (  j₉ <= j₉
                                                      && 0 <= j₉
                                                      && j₉ < j₂₂ + 1
                                                       ==> i₈ < 100000))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (!(i₂₁ < 100000
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 1 <= 100000
                                                  && (forall i₁₄: int, j₁₅: int ::
                                                        (  j₁₅ <= j₁₅
                                                          && 0 <= j₁₅
                                                          && j₁₅ < 0
                                                           ==> i₁₄ < 100000))
                                                  && (forall i₂₃: int, j₂₄: int ::
                                                        (  true
                                                          && 0 <= j₂₄
                                                          && i₂₃ <= 100000
                                                          && (forall i₁₄: int, j₁₅: int ::
                                                                (  j₁₅ <= j₁₅
                                                                  && 0 <= j₁₅
                                                                  && j₁₅ < j₂₄
                                                                   ==> i₁₄ < 100000))
                                                           ==> (i₂₃ < 100000
                                                               ==> a₂₀[j₂₄] == b₁₈[2 * j₂₄ + 1]
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= j₂₄ + 1
                                                                    && i₂₃ + 2 <= 100000
                                                                    && (forall i₁₄: int, j₁₅: int ::
                                                                          (  j₁₅ <= j₁₅
                                                                            && 0 <= j₁₅
                                                                            && j₁₅ < j₂₄ + 1
                                                                             ==> i₁₄ < 100000))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(i₂₃ < 100000
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true))))))))))))));


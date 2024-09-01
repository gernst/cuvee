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
              && (forall x₆: int ::
                    ((exists i₅: int ::
                            x₆ == i₅
                            && 0 <= i₅
                            && i₅ < 0)
                       ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                              i₅ < 100000
                              && x₆ == i₅
                              && 0 <= i₅
                              && i₅ < 0
                              && a[x₆] == __VERIFIER_nondet_int₁₄)))
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
              && (forall a₁₆: [int]int, i₁₇: int ::
                    (  true
                      && 0 <= i₁₇
                      && i₁₇ <= 100000
                      && (forall x₆: int ::
                            ((exists i₅: int ::
                                    x₆ == i₅
                                    && 0 <= i₅
                                    && i₅ < i₁₇)
                               ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                      i₅ < 100000
                                      && x₆ == i₅
                                      && 0 <= i₅
                                      && i₅ < i₁₇
                                      && a₁₆[x₆] == __VERIFIER_nondet_int₁₄)))
                      && (forall x₆: int ::
                            (!((exists i₅: int ::
                                    x₆ == i₅
                                    && 0 <= i₅
                                    && i₅ < i₁₇)
                            )
                               ==> a₁₆[x₆] == a[x₆]))
                      && (forall i₅: int ::
                            (  i₅ <= i₅
                              && 0 <= i₅
                              && i₅ < i₁₇
                               ==> i₅ < 100000))
                       ==> (i₁₇ < 100000
                           ==> (forall __VERIFIER_nondet_int₁: int ::
                                  true
                                  && 0 <= i₁₇ + 1
                                  && i₁₇ + 1 <= 100000
                                  && (forall x₆: int ::
                                        ((exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₇ + 1)
                                           ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                  i₅ < 100000
                                                  && x₆ == i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₁₇ + 1
                                                  && a₁₆[i₁₇ := __VERIFIER_nondet_int₁][x₆] == __VERIFIER_nondet_int₁₄)))
                                  && (forall x₆: int ::
                                        (!((exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₇ + 1)
                                        )
                                           ==> a₁₆[i₁₇ := __VERIFIER_nondet_int₁][x₆] == a[x₆]))
                                  && (forall i₅: int ::
                                        (  i₅ <= i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₇ + 1
                                           ==> i₅ < 100000))
                                  && true
                                  && (true
                                     ==> true)))
                        && (!(i₁₇ < 100000
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
                                                && b[x₁₀] == a₁₆[99999 + -i₉])))
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
                                && (forall b₁₈: [int]int, i₁₉: int ::
                                      (  true
                                        && 0 <= i₁₉
                                        && i₁₉ <= 100000
                                        && (forall x₁₀: int ::
                                              ((exists i₉: int ::
                                                      x₁₀ == i₉
                                                      && 0 <= i₉
                                                      && i₉ < i₁₉)
                                                 ==> (exists i₉: int ::
                                                        i₉ < 100000
                                                        && x₁₀ == i₉
                                                        && 0 <= i₉
                                                        && i₉ < i₁₉
                                                        && b₁₈[x₁₀] == a₁₆[99999 + -i₉])))
                                        && (forall x₁₀: int ::
                                              (!((exists i₉: int ::
                                                      x₁₀ == i₉
                                                      && 0 <= i₉
                                                      && i₉ < i₁₉)
                                              )
                                                 ==> b₁₈[x₁₀] == b[x₁₀]))
                                        && (forall i₉: int ::
                                              (  i₉ <= i₉
                                                && 0 <= i₉
                                                && i₉ < i₁₉
                                                 ==> i₉ < 100000))
                                         ==> (i₁₉ < 100000
                                             ==> true
                                              && 0 <= i₁₉ + 1
                                              && i₁₉ + 1 <= 100000
                                              && (forall x₁₀: int ::
                                                    ((exists i₉: int ::
                                                            x₁₀ == i₉
                                                            && 0 <= i₉
                                                            && i₉ < i₁₉ + 1)
                                                       ==> (exists i₉: int ::
                                                              i₉ < 100000
                                                              && x₁₀ == i₉
                                                              && 0 <= i₉
                                                              && i₉ < i₁₉ + 1
                                                              && b₁₈[i₁₉ := a₁₆[100000 - i₁₉ - 1]][x₁₀] == a₁₆[99999 + -i₉])))
                                              && (forall x₁₀: int ::
                                                    (!((exists i₉: int ::
                                                            x₁₀ == i₉
                                                            && 0 <= i₉
                                                            && i₉ < i₁₉ + 1)
                                                    )
                                                       ==> b₁₈[i₁₉ := a₁₆[100000 - i₁₉ - 1]][x₁₀] == b[x₁₀]))
                                              && (forall i₉: int ::
                                                    (  i₉ <= i₉
                                                      && 0 <= i₉
                                                      && i₉ < i₁₉ + 1
                                                       ==> i₉ < 100000))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (!(i₁₉ < 100000
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₁₄: int ::
                                                        (  x₁₄ <= x₁₄
                                                          && 0 <= x₁₄
                                                          && x₁₄ < 0
                                                           ==> x₁₄ < 100000))
                                                  && (forall x₂₀: int ::
                                                        (  true
                                                          && 0 <= x₂₀
                                                          && x₂₀ <= 100000
                                                          && (forall x₁₄: int ::
                                                                (  x₁₄ <= x₁₄
                                                                  && 0 <= x₁₄
                                                                  && x₁₄ < x₂₀
                                                                   ==> x₁₄ < 100000))
                                                           ==> (x₂₀ < 100000
                                                               ==> a₁₆[x₂₀] == b₁₈[100000 - x₂₀ - 1]
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= x₂₀ + 1
                                                                    && x₂₀ + 1 <= 100000
                                                                    && (forall x₁₄: int ::
                                                                          (  x₁₄ <= x₁₄
                                                                            && 0 <= x₁₄
                                                                            && x₁₄ < x₂₀ + 1
                                                                             ==> x₁₄ < 100000))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(x₂₀ < 100000
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true))))))))))))));


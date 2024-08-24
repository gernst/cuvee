data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₅: int ::
        N₁₅ <= 0
        || (forall a: [int]int ::
              (N₁₅ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₁₅
                  && (forall x₆: int, i₅: int ::
                        (  x₆ == i₅
                          && 0 <= i₅
                          && i₅ < 0
                           ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                  i₅ < N₁₅
                                  && x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0
                                  && a[x₆] == __VERIFIER_nondet_int₁₄)))
                  && (forall x₆: int ::
                          (exists i₅: int ::
                                  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                          || a[x₆] == a[x₆])
                  && (forall i₅: int ::
                        (  0 <= i₅
                          && i₅ < 0
                           ==> i₅ < N₁₅))
                  && (forall a₁₆: [int]int, i₁₇: int ::
                        (  0 <= i₁₇
                          && i₁₇ <= N₁₅
                          && (forall x₆: int, i₅: int ::
                                (  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < i₁₇
                                   ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                          i₅ < N₁₅
                                          && x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₇
                                          && a₁₆[x₆] == __VERIFIER_nondet_int₁₄)))
                          && (forall x₆: int ::
                                  (exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₇)
                                  || a₁₆[x₆] == a[x₆])
                          && (forall i₅: int ::
                                (  0 <= i₅
                                  && i₅ < i₁₇
                                   ==> i₅ < N₁₅))
                           ==> (forall __VERIFIER_nondet_int₁: int ::
                                  (i₁₇ < N₁₅
                                     ==> 0 <= i₁₇ + 1
                                      && i₁₇ + 1 <= N₁₅
                                      && (forall x₆: int, i₅: int ::
                                            (  x₆ == i₅
                                              && 0 <= i₅
                                              && i₅ < i₁₇ + 1
                                               ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                      i₅ < N₁₅
                                                      && x₆ == i₅
                                                      && 0 <= i₅
                                                      && i₅ < i₁₇ + 1
                                                      && a₁₆[i₁₇ := __VERIFIER_nondet_int₁][x₆] == __VERIFIER_nondet_int₁₄)))
                                      && (forall x₆: int ::
                                              (exists i₅: int ::
                                                      x₆ == i₅
                                                      && 0 <= i₅
                                                      && i₅ < i₁₇ + 1)
                                              || a₁₆[i₁₇ := __VERIFIER_nondet_int₁][x₆] == a[x₆])
                                      && (forall i₅: int ::
                                            (  0 <= i₅
                                              && i₅ < i₁₇ + 1
                                               ==> i₅ < N₁₅))))
                            &&   i₁₇ < N₁₅
                              ||   0 <= 0
                                && 0 <= N₁₅
                                && (forall x₁₀: int, i₉: int ::
                                      (  x₁₀ == i₉
                                        && 0 <= i₉
                                        && i₉ < 0
                                         ==> (exists i₉: int ::
                                                  N₁₅ < a₁₆[i₉]
                                                  && i₉ < N₁₅
                                                  && x₁₀ == i₉
                                                  && 0 <= i₉
                                                  && i₉ < 0
                                                  && a₁₆[x₁₀] == a₁₆[i₉])
                                          || (exists i₉: int ::
                                                (N₁₅ < a₁₆[i₉]
                                                   ==> false))))
                                && (forall x₁₀: int ::
                                        (exists i₉: int ::
                                                x₁₀ == i₉
                                                && 0 <= i₉
                                                && i₉ < 0)
                                        || a₁₆[x₁₀] == a₁₆[x₁₀])
                                && (forall i₉: int ::
                                      (  0 <= i₉
                                        && i₉ < 0
                                         ==> i₉ < N₁₅))
                                && (forall a₁₈: [int]int, i₁₉: int ::
                                      (  0 <= i₁₉
                                        && i₁₉ <= N₁₅
                                        && (forall x₁₀: int, i₉: int ::
                                              (  x₁₀ == i₉
                                                && 0 <= i₉
                                                && i₉ < i₁₉
                                                 ==> (exists i₉: int ::
                                                          N₁₅ < a₁₈[i₉]
                                                          && i₉ < N₁₅
                                                          && x₁₀ == i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₁₉
                                                          && a₁₈[x₁₀] == a₁₆[i₉])
                                                  || (exists i₉: int ::
                                                        (N₁₅ < a₁₈[i₉]
                                                           ==> false))))
                                        && (forall x₁₀: int ::
                                                (exists i₉: int ::
                                                        x₁₀ == i₉
                                                        && 0 <= i₉
                                                        && i₉ < i₁₉)
                                                || a₁₈[x₁₀] == a₁₆[x₁₀])
                                        && (forall i₉: int ::
                                              (  0 <= i₉
                                                && i₉ < i₁₉
                                                 ==> i₉ < N₁₅))
                                         ==> (i₁₉ < N₁₅
                                             ==> (N₁₅ < a₁₈[i₁₉]
                                                 ==> 0 <= i₁₉ + 1
                                                  && i₁₉ + 1 <= N₁₅
                                                  && (forall x₁₀: int, i₉: int ::
                                                        (  x₁₀ == i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₁₉ + 1
                                                           ==> (exists i₉: int ::
                                                                    N₁₅ < a₁₈[i₁₉ := a₁₈[i₁₉]][i₉]
                                                                    && i₉ < N₁₅
                                                                    && x₁₀ == i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₁₉ + 1
                                                                    && a₁₈[i₁₉ := a₁₈[i₁₉]][x₁₀] == a₁₆[i₉])
                                                            || (exists i₉: int ::
                                                                  (N₁₅ < a₁₈[i₁₉ := a₁₈[i₁₉]][i₉]
                                                                     ==> false))))
                                                  && (forall x₁₀: int ::
                                                          (exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₁₉ + 1)
                                                          || a₁₈[i₁₉ := a₁₈[i₁₉]][x₁₀] == a₁₆[x₁₀])
                                                  && (forall i₉: int ::
                                                        (  0 <= i₉
                                                          && i₉ < i₁₉ + 1
                                                           ==> i₉ < N₁₅)))
                                              &&   N₁₅ < a₁₈[i₁₉]
                                                ||   0 <= i₁₉ + 1
                                                  && i₁₉ + 1 <= N₁₅
                                                  && (forall x₁₀: int, i₉: int ::
                                                        (  x₁₀ == i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₁₉ + 1
                                                           ==> (exists i₉: int ::
                                                                    N₁₅ < a₁₈[i₁₉ := N₁₅][i₉]
                                                                    && i₉ < N₁₅
                                                                    && x₁₀ == i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₁₉ + 1
                                                                    && a₁₈[i₁₉ := N₁₅][x₁₀] == a₁₆[i₉])
                                                            || (exists i₉: int ::
                                                                  (N₁₅ < a₁₈[i₁₉ := N₁₅][i₉]
                                                                     ==> false))))
                                                  && (forall x₁₀: int ::
                                                          (exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₁₉ + 1)
                                                          || a₁₈[i₁₉ := N₁₅][x₁₀] == a₁₆[x₁₀])
                                                  && (forall i₉: int ::
                                                        (  0 <= i₉
                                                          && i₉ < i₁₉ + 1
                                                           ==> i₉ < N₁₅)))
                                          &&   i₁₉ < N₁₅
                                            ||   0 <= 0
                                              && 0 <= N₁₅
                                              && (forall i₁₃: int ::
                                                    (  0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> i₁₃ < N₁₅))
                                              && (forall i₂₀: int ::
                                                    (  0 <= i₂₀
                                                      && i₂₀ <= N₁₅
                                                      && (forall i₁₃: int ::
                                                            (  0 <= i₁₃
                                                              && i₁₃ < i₂₀
                                                               ==> i₁₃ < N₁₅))
                                                       ==> (i₂₀ < N₁₅
                                                         ==> a₁₈[i₂₀] <= N₁₅
                                                          && 0 <= i₂₀ + 1
                                                          && i₂₀ + 1 <= N₁₅
                                                          && (forall i₁₃: int ::
                                                                (  0 <= i₁₃
                                                                  && i₁₃ < i₂₀ + 1
                                                                   ==> i₁₃ < N₁₅))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall N₁₅: int ::
          (true
             ==> (N₁₅ <= 0
                 ==> true)
              && (!(N₁₅ <= 0
              )
                 ==> true
                  && (N₁₅ <= 2147483647 / 4
                     ==> (forall a: [int]int ::
                            true
                            && 0 <= 0
                            && 0 <= N₁₅
                            && (forall x₆: int ::
                                  ((exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < 0)
                                     ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                            i₅ < N₁₅
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
                                     ==> i₅ < N₁₅))
                            && (forall a₁₆: [int]int, i₁₇: int ::
                                  (  true
                                    && 0 <= i₁₇
                                    && i₁₇ <= N₁₅
                                    && (forall x₆: int ::
                                          ((exists i₅: int ::
                                                  x₆ == i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₁₇)
                                             ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                    i₅ < N₁₅
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
                                             ==> i₅ < N₁₅))
                                     ==> (i₁₇ < N₁₅
                                         ==> (forall __VERIFIER_nondet_int₁: int ::
                                                true
                                                && 0 <= i₁₇ + 1
                                                && i₁₇ + 1 <= N₁₅
                                                && (forall x₆: int ::
                                                      ((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 0 <= i₅
                                                              && i₅ < i₁₇ + 1)
                                                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                                i₅ < N₁₅
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
                                                         ==> i₅ < N₁₅))
                                                && true
                                                && (true
                                                   ==> true)))
                                      && (!(i₁₇ < N₁₅
                                      )
                                         ==> true
                                          && (true
                                             ==> true
                                              && 0 <= 0
                                              && 0 <= N₁₅
                                              && (forall x₁₀: int ::
                                                    ((exists i₉: int ::
                                                            x₁₀ == i₉
                                                            && 0 <= i₉
                                                            && i₉ < 0)
                                                       ==> (exists i₉: int ::
                                                                a₁₆[i₉] < N₁₅
                                                                && i₉ < N₁₅
                                                                && x₁₀ == i₉
                                                                && 0 <= i₉
                                                                && i₉ < 0
                                                                && a₁₆[x₁₀] == a₁₆[i₉])
                                                        || (exists i₉: int ::
                                                                !(a₁₆[i₉] < N₁₅
                                                                )
                                                                && i₉ < N₁₅
                                                                && x₁₀ == i₉
                                                                && 0 <= i₉
                                                                && i₉ < 0
                                                                && a₁₆[x₁₀] == N₁₅)))
                                              && (forall x₁₀: int ::
                                                    (!((exists i₉: int ::
                                                            x₁₀ == i₉
                                                            && 0 <= i₉
                                                            && i₉ < 0)
                                                    )
                                                       ==> a₁₆[x₁₀] == a₁₆[x₁₀]))
                                              && (forall i₉: int ::
                                                    (  i₉ <= i₉
                                                      && 0 <= i₉
                                                      && i₉ < 0
                                                       ==> i₉ < N₁₅))
                                              && (forall a₁₈: [int]int, i₁₉: int ::
                                                    (  true
                                                      && 0 <= i₁₉
                                                      && i₁₉ <= N₁₅
                                                      && (forall x₁₀: int ::
                                                            ((exists i₉: int ::
                                                                    x₁₀ == i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₁₉)
                                                               ==> (exists i₉: int ::
                                                                        a₁₈[i₉] < N₁₅
                                                                        && i₉ < N₁₅
                                                                        && x₁₀ == i₉
                                                                        && 0 <= i₉
                                                                        && i₉ < i₁₉
                                                                        && a₁₈[x₁₀] == a₁₆[i₉])
                                                                || (exists i₉: int ::
                                                                        !(a₁₈[i₉] < N₁₅
                                                                        )
                                                                        && i₉ < N₁₅
                                                                        && x₁₀ == i₉
                                                                        && 0 <= i₉
                                                                        && i₉ < i₁₉
                                                                        && a₁₈[x₁₀] == N₁₅)))
                                                      && (forall x₁₀: int ::
                                                            (!((exists i₉: int ::
                                                                    x₁₀ == i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₁₉)
                                                            )
                                                               ==> a₁₈[x₁₀] == a₁₆[x₁₀]))
                                                      && (forall i₉: int ::
                                                            (  i₉ <= i₉
                                                              && 0 <= i₉
                                                              && i₉ < i₁₉
                                                               ==> i₉ < N₁₅))
                                                       ==> (i₁₉ < N₁₅
                                                           ==> (a₁₈[i₁₉] < N₁₅
                                                               ==> true
                                                                && 0 <= i₁₉ + 1
                                                                && i₁₉ + 1 <= N₁₅
                                                                && (forall x₁₀: int ::
                                                                      ((exists i₉: int ::
                                                                              x₁₀ == i₉
                                                                              && 0 <= i₉
                                                                              && i₉ < i₁₉ + 1)
                                                                         ==> (exists i₉: int ::
                                                                                  a₁₈[i₁₉ := a₁₈[i₁₉]][i₉] < N₁₅
                                                                                  && i₉ < N₁₅
                                                                                  && x₁₀ == i₉
                                                                                  && 0 <= i₉
                                                                                  && i₉ < i₁₉ + 1
                                                                                  && a₁₈[i₁₉ := a₁₈[i₁₉]][x₁₀] == a₁₆[i₉])
                                                                          || (exists i₉: int ::
                                                                                  !(a₁₈[i₁₉ := a₁₈[i₁₉]][i₉] < N₁₅
                                                                                  )
                                                                                  && i₉ < N₁₅
                                                                                  && x₁₀ == i₉
                                                                                  && 0 <= i₉
                                                                                  && i₉ < i₁₉ + 1
                                                                                  && a₁₈[i₁₉ := a₁₈[i₁₉]][x₁₀] == N₁₅)))
                                                                && (forall x₁₀: int ::
                                                                      (!((exists i₉: int ::
                                                                              x₁₀ == i₉
                                                                              && 0 <= i₉
                                                                              && i₉ < i₁₉ + 1)
                                                                      )
                                                                         ==> a₁₈[i₁₉ := a₁₈[i₁₉]][x₁₀] == a₁₆[x₁₀]))
                                                                && (forall i₉: int ::
                                                                      (  i₉ <= i₉
                                                                        && 0 <= i₉
                                                                        && i₉ < i₁₉ + 1
                                                                         ==> i₉ < N₁₅))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (!(a₁₈[i₁₉] < N₁₅
                                                            )
                                                               ==> true
                                                                && 0 <= i₁₉ + 1
                                                                && i₁₉ + 1 <= N₁₅
                                                                && (forall x₁₀: int ::
                                                                      ((exists i₉: int ::
                                                                              x₁₀ == i₉
                                                                              && 0 <= i₉
                                                                              && i₉ < i₁₉ + 1)
                                                                         ==> (exists i₉: int ::
                                                                                  a₁₈[i₁₉ := N₁₅][i₉] < N₁₅
                                                                                  && i₉ < N₁₅
                                                                                  && x₁₀ == i₉
                                                                                  && 0 <= i₉
                                                                                  && i₉ < i₁₉ + 1
                                                                                  && a₁₈[i₁₉ := N₁₅][x₁₀] == a₁₆[i₉])
                                                                          || (exists i₉: int ::
                                                                                  !(a₁₈[i₁₉ := N₁₅][i₉] < N₁₅
                                                                                  )
                                                                                  && i₉ < N₁₅
                                                                                  && x₁₀ == i₉
                                                                                  && 0 <= i₉
                                                                                  && i₉ < i₁₉ + 1
                                                                                  && a₁₈[i₁₉ := N₁₅][x₁₀] == N₁₅)))
                                                                && (forall x₁₀: int ::
                                                                      (!((exists i₉: int ::
                                                                              x₁₀ == i₉
                                                                              && 0 <= i₉
                                                                              && i₉ < i₁₉ + 1)
                                                                      )
                                                                         ==> a₁₈[i₁₉ := N₁₅][x₁₀] == a₁₆[x₁₀]))
                                                                && (forall i₉: int ::
                                                                      (  i₉ <= i₉
                                                                        && 0 <= i₉
                                                                        && i₉ < i₁₉ + 1
                                                                         ==> i₉ < N₁₅))
                                                                && true
                                                                && (true
                                                                   ==> true)))
                                                        && (!(i₁₉ < N₁₅
                                                        )
                                                           ==> true
                                                            && (true
                                                               ==> true
                                                                && 0 <= 0
                                                                && 0 <= N₁₅
                                                                && (forall i₁₃: int ::
                                                                      (  i₁₃ <= i₁₃
                                                                        && 0 <= i₁₃
                                                                        && i₁₃ < 0
                                                                         ==> i₁₃ < N₁₅))
                                                                && (forall i₂₀: int ::
                                                                      (  true
                                                                        && 0 <= i₂₀
                                                                        && i₂₀ <= N₁₅
                                                                        && (forall i₁₃: int ::
                                                                              (  i₁₃ <= i₁₃
                                                                                && 0 <= i₁₃
                                                                                && i₁₃ < i₂₀
                                                                                 ==> i₁₃ < N₁₅))
                                                                         ==> (i₂₀ < N₁₅
                                                                             ==> a₁₈[i₂₀] <= N₁₅
                                                                              && (true
                                                                                 ==> true
                                                                                  && 0 <= i₂₀ + 1
                                                                                  && i₂₀ + 1 <= N₁₅
                                                                                  && (forall i₁₃: int ::
                                                                                        (  i₁₃ <= i₁₃
                                                                                          && 0 <= i₁₃
                                                                                          && i₁₃ < i₂₀ + 1
                                                                                           ==> i₁₃ < N₁₅))
                                                                                  && true
                                                                                  && (true
                                                                                     ==> true)))
                                                                          && (!(i₂₀ < N₁₅
                                                                          )
                                                                             ==> true
                                                                              && (true
                                                                                 ==> true))))))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall N₁₇: int ::
          (true
             ==> (N₁₇ <= 0
                 ==> true)
              && (!(N₁₇ <= 0
              )
                 ==> true
                  && (N₁₇ <= 2147483647 / 4
                     ==> (forall sum: [int]int ::
                          (forall a: [int]int ::
                                  true
                                  && 0 <= 0
                                  && 0 <= N₁₇
                                  && (forall x₆: int ::
                                        ((exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < 0)
                                           ==> (exists i₅: int ::
                                                  i₅ < N₁₇
                                                  && x₆ == i₅
                                                  && 0 <= i₅
                                                  && i₅ < 0
                                                  && a[x₆] == 1)))
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
                                           ==> i₅ < N₁₇))
                                  && (forall a₁₈: [int]int, i₁₉: int ::
                                        (  true
                                          && 0 <= i₁₉
                                          && i₁₉ <= N₁₇
                                          && (forall x₆: int ::
                                                ((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₁₉)
                                                   ==> (exists i₅: int ::
                                                          i₅ < N₁₇
                                                          && x₆ == i₅
                                                          && 0 <= i₅
                                                          && i₅ < i₁₉
                                                          && a₁₈[x₆] == 1)))
                                          && (forall x₆: int ::
                                                (!((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₁₉)
                                                )
                                                   ==> a₁₈[x₆] == a[x₆]))
                                          && (forall i₅: int ::
                                                (  i₅ <= i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₁₉
                                                   ==> i₅ < N₁₇))
                                           ==> (i₁₉ < N₁₇
                                               ==> true
                                                && 0 <= i₁₉ + 1
                                                && i₁₉ + 1 <= N₁₇
                                                && (forall x₆: int ::
                                                      ((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 0 <= i₅
                                                              && i₅ < i₁₉ + 1)
                                                         ==> (exists i₅: int ::
                                                                i₅ < N₁₇
                                                                && x₆ == i₅
                                                                && 0 <= i₅
                                                                && i₅ < i₁₉ + 1
                                                                && a₁₈[i₁₉ := 1][x₆] == 1)))
                                                && (forall x₆: int ::
                                                      (!((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 0 <= i₅
                                                              && i₅ < i₁₉ + 1)
                                                      )
                                                         ==> a₁₈[i₁₉ := 1][x₆] == a[x₆]))
                                                && (forall i₅: int ::
                                                      (  i₅ <= i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₁₉ + 1
                                                         ==> i₅ < N₁₇))
                                                && true
                                                && (true
                                                   ==> true))
                                            && (!(i₁₉ < N₁₇
                                            )
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 0 <= 0
                                                    && 0 <= N₁₇
                                                    && (forall x₁₀: int ::
                                                          ((exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < 0)
                                                             ==> (exists i₉: int ::
                                                                      a₁₈[i₉] == 1
                                                                      && i₉ < N₁₇
                                                                      && x₁₀ == i₉
                                                                      && 0 <= i₉
                                                                      && i₉ < 0
                                                                      && a₁₈[x₁₀] == 4 + a₁₈[i₉])
                                                              || (exists i₉: int ::
                                                                      a₁₈[i₉] != 1
                                                                      && i₉ < N₁₇
                                                                      && x₁₀ == i₉
                                                                      && 0 <= i₉
                                                                      && i₉ < 0
                                                                      && a₁₈[x₁₀] == -1 + a₁₈[i₉])))
                                                    && (forall x₁₀: int ::
                                                          (!((exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < 0)
                                                          )
                                                             ==> a₁₈[x₁₀] == a₁₈[x₁₀]))
                                                    && (forall i₉: int ::
                                                          (  i₉ <= i₉
                                                            && 0 <= i₉
                                                            && i₉ < 0
                                                             ==> i₉ < N₁₇))
                                                    && (forall a₂₀: [int]int, i₂₁: int ::
                                                          (  true
                                                            && 0 <= i₂₁
                                                            && i₂₁ <= N₁₇
                                                            && (forall x₁₀: int ::
                                                                  ((exists i₉: int ::
                                                                          x₁₀ == i₉
                                                                          && 0 <= i₉
                                                                          && i₉ < i₂₁)
                                                                     ==> (exists i₉: int ::
                                                                              a₂₀[i₉] == 1
                                                                              && i₉ < N₁₇
                                                                              && x₁₀ == i₉
                                                                              && 0 <= i₉
                                                                              && i₉ < i₂₁
                                                                              && a₂₀[x₁₀] == 4 + a₁₈[i₉])
                                                                      || (exists i₉: int ::
                                                                              a₂₀[i₉] != 1
                                                                              && i₉ < N₁₇
                                                                              && x₁₀ == i₉
                                                                              && 0 <= i₉
                                                                              && i₉ < i₂₁
                                                                              && a₂₀[x₁₀] == -1 + a₁₈[i₉])))
                                                            && (forall x₁₀: int ::
                                                                  (!((exists i₉: int ::
                                                                          x₁₀ == i₉
                                                                          && 0 <= i₉
                                                                          && i₉ < i₂₁)
                                                                  )
                                                                     ==> a₂₀[x₁₀] == a₁₈[x₁₀]))
                                                            && (forall i₉: int ::
                                                                  (  i₉ <= i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₂₁
                                                                     ==> i₉ < N₁₇))
                                                             ==> (i₂₁ < N₁₇
                                                                 ==> (a₂₀[i₂₁] == 1
                                                                     ==> true
                                                                      && 0 <= i₂₁ + 1
                                                                      && i₂₁ + 1 <= N₁₇
                                                                      && (forall x₁₀: int ::
                                                                            ((exists i₉: int ::
                                                                                    x₁₀ == i₉
                                                                                    && 0 <= i₉
                                                                                    && i₉ < i₂₁ + 1)
                                                                               ==> (exists i₉: int ::
                                                                                        a₂₀[i₂₁ := a₂₀[i₂₁] + 4][i₉] == 1
                                                                                        && i₉ < N₁₇
                                                                                        && x₁₀ == i₉
                                                                                        && 0 <= i₉
                                                                                        && i₉ < i₂₁ + 1
                                                                                        && a₂₀[i₂₁ := a₂₀[i₂₁] + 4][x₁₀] == 4 + a₁₈[i₉])
                                                                                || (exists i₉: int ::
                                                                                        a₂₀[i₂₁ := a₂₀[i₂₁] + 4][i₉] != 1
                                                                                        && i₉ < N₁₇
                                                                                        && x₁₀ == i₉
                                                                                        && 0 <= i₉
                                                                                        && i₉ < i₂₁ + 1
                                                                                        && a₂₀[i₂₁ := a₂₀[i₂₁] + 4][x₁₀] == -1 + a₁₈[i₉])))
                                                                      && (forall x₁₀: int ::
                                                                            (!((exists i₉: int ::
                                                                                    x₁₀ == i₉
                                                                                    && 0 <= i₉
                                                                                    && i₉ < i₂₁ + 1)
                                                                            )
                                                                               ==> a₂₀[i₂₁ := a₂₀[i₂₁] + 4][x₁₀] == a₁₈[x₁₀]))
                                                                      && (forall i₉: int ::
                                                                            (  i₉ <= i₉
                                                                              && 0 <= i₉
                                                                              && i₉ < i₂₁ + 1
                                                                               ==> i₉ < N₁₇))
                                                                      && true
                                                                      && (true
                                                                         ==> true))
                                                                  && (a₂₀[i₂₁] != 1
                                                                     ==> true
                                                                      && 0 <= i₂₁ + 1
                                                                      && i₂₁ + 1 <= N₁₇
                                                                      && (forall x₁₀: int ::
                                                                            ((exists i₉: int ::
                                                                                    x₁₀ == i₉
                                                                                    && 0 <= i₉
                                                                                    && i₉ < i₂₁ + 1)
                                                                               ==> (exists i₉: int ::
                                                                                        a₂₀[i₂₁ := a₂₀[i₂₁] - 1][i₉] == 1
                                                                                        && i₉ < N₁₇
                                                                                        && x₁₀ == i₉
                                                                                        && 0 <= i₉
                                                                                        && i₉ < i₂₁ + 1
                                                                                        && a₂₀[i₂₁ := a₂₀[i₂₁] - 1][x₁₀] == 4 + a₁₈[i₉])
                                                                                || (exists i₉: int ::
                                                                                        a₂₀[i₂₁ := a₂₀[i₂₁] - 1][i₉] != 1
                                                                                        && i₉ < N₁₇
                                                                                        && x₁₀ == i₉
                                                                                        && 0 <= i₉
                                                                                        && i₉ < i₂₁ + 1
                                                                                        && a₂₀[i₂₁ := a₂₀[i₂₁] - 1][x₁₀] == -1 + a₁₈[i₉])))
                                                                      && (forall x₁₀: int ::
                                                                            (!((exists i₉: int ::
                                                                                    x₁₀ == i₉
                                                                                    && 0 <= i₉
                                                                                    && i₉ < i₂₁ + 1)
                                                                            )
                                                                               ==> a₂₀[i₂₁ := a₂₀[i₂₁] - 1][x₁₀] == a₁₈[x₁₀]))
                                                                      && (forall i₉: int ::
                                                                            (  i₉ <= i₉
                                                                              && 0 <= i₉
                                                                              && i₉ < i₂₁ + 1
                                                                               ==> i₉ < N₁₇))
                                                                      && true
                                                                      && (true
                                                                         ==> true)))
                                                              && (!(i₂₁ < N₁₇
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> true
                                                                      && 0 <= 0
                                                                      && 0 <= N₁₇
                                                                      && (forall x₁₄: int ::
                                                                            (x₁₄ == 0
                                                                               ==> (exists i₁₃: int ::
                                                                                      i₁₃ < N₁₇
                                                                                      && x₁₄ == 0
                                                                                      && sum[0 := 0][x₁₄] == a₂₀[i₁₃] + sum[0 := 0][0])))
                                                                      && (forall x₁₄: int ::
                                                                            (x₁₄ != 0
                                                                               ==> sum[0 := 0][x₁₄] == sum[0 := 0][x₁₄]))
                                                                      && (forall i₁₃: int ::
                                                                            (  i₁₃ <= i₁₃
                                                                              && 0 <= i₁₃
                                                                              && i₁₃ < 0
                                                                               ==> i₁₃ < N₁₇))
                                                                      && (forall sum₂₂: [int]int, i₂₃: int ::
                                                                            (  true
                                                                              && 0 <= i₂₃
                                                                              && i₂₃ <= N₁₇
                                                                              && (forall x₁₄: int ::
                                                                                    (x₁₄ == 0
                                                                                       ==> (exists i₁₃: int ::
                                                                                              i₁₃ < N₁₇
                                                                                              && x₁₄ == 0
                                                                                              && sum₂₂[x₁₄] == a₂₀[i₁₃] + sum[0 := 0][0])))
                                                                              && (forall x₁₄: int ::
                                                                                    (x₁₄ != 0
                                                                                       ==> sum₂₂[x₁₄] == sum[0 := 0][x₁₄]))
                                                                              && (forall i₁₃: int ::
                                                                                    (  i₁₃ <= i₁₃
                                                                                      && 0 <= i₁₃
                                                                                      && i₁₃ < i₂₃
                                                                                       ==> i₁₃ < N₁₇))
                                                                               ==> (i₂₃ < N₁₇
                                                                                   ==> true
                                                                                    && 0 <= i₂₃ + 1
                                                                                    && i₂₃ + 1 <= N₁₇
                                                                                    && (forall x₁₄: int ::
                                                                                          (x₁₄ == 0
                                                                                             ==> (exists i₁₃: int ::
                                                                                                    i₁₃ < N₁₇
                                                                                                    && x₁₄ == 0
                                                                                                    && sum₂₂[0 := sum₂₂[0] + a₂₀[i₂₃]][x₁₄] == a₂₀[i₁₃] + sum[0 := 0][0])))
                                                                                    && (forall x₁₄: int ::
                                                                                          (x₁₄ != 0
                                                                                             ==> sum₂₂[0 := sum₂₂[0] + a₂₀[i₂₃]][x₁₄] == sum[0 := 0][x₁₄]))
                                                                                    && (forall i₁₃: int ::
                                                                                          (  i₁₃ <= i₁₃
                                                                                            && 0 <= i₁₃
                                                                                            && i₁₃ < i₂₃ + 1
                                                                                             ==> i₁₃ < N₁₇))
                                                                                    && true
                                                                                    && (true
                                                                                       ==> true))
                                                                                && (!(i₂₃ < N₁₇
                                                                                )
                                                                                   ==> true
                                                                                    && (true
                                                                                       ==> sum₂₂[0] == 5 * N₁₇
                                                                                        && (true
                                                                                           ==> true))))))))))))))))))));


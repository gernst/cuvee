data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall N₁₉: int ::
          (true
             ==> (N₁₉ <= 0
                 ==> true)
              && (!(N₁₉ <= 0
              )
                 ==> true
                  && (N₁₉ <= 2147483647 / 4
                     ==> (forall sum: [int]int ::
                          (forall a: [int]int ::
                                  true
                                  && 0 <= 0
                                  && 0 <= N₁₉
                                  && (forall x₆: int ::
                                        ((exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < 0)
                                           ==> (exists i₅: int ::
                                                  i₅ < N₁₉
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
                                           ==> i₅ < N₁₉))
                                  && (forall a₂₀: [int]int, i₂₁: int ::
                                        (  true
                                          && 0 <= i₂₁
                                          && i₂₁ <= N₁₉
                                          && (forall x₆: int ::
                                                ((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₂₁)
                                                   ==> (exists i₅: int ::
                                                          i₅ < N₁₉
                                                          && x₆ == i₅
                                                          && 0 <= i₅
                                                          && i₅ < i₂₁
                                                          && a₂₀[x₆] == 1)))
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
                                                   ==> i₅ < N₁₉))
                                           ==> (i₂₁ < N₁₉
                                               ==> true
                                                && 0 <= i₂₁ + 1
                                                && i₂₁ + 1 <= N₁₉
                                                && (forall x₆: int ::
                                                      ((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 0 <= i₅
                                                              && i₅ < i₂₁ + 1)
                                                         ==> (exists i₅: int ::
                                                                i₅ < N₁₉
                                                                && x₆ == i₅
                                                                && 0 <= i₅
                                                                && i₅ < i₂₁ + 1
                                                                && a₂₀[i₂₁ := 1][x₆] == 1)))
                                                && (forall x₆: int ::
                                                      (!((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 0 <= i₅
                                                              && i₅ < i₂₁ + 1)
                                                      )
                                                         ==> a₂₀[i₂₁ := 1][x₆] == a[x₆]))
                                                && (forall i₅: int ::
                                                      (  i₅ <= i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₂₁ + 1
                                                         ==> i₅ < N₁₉))
                                                && true
                                                && (true
                                                   ==> true))
                                            && (!(i₂₁ < N₁₉
                                            )
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 0 <= 0
                                                    && 0 <= N₁₉
                                                    && (forall x₁₀: int ::
                                                          (x₁₀ == 0
                                                             ==> (exists i₉: int ::
                                                                    i₉ < N₁₉
                                                                    && x₁₀ == 0
                                                                    && sum[0 := 0][x₁₀] == a₂₀[i₉] + sum[0 := 0][0])))
                                                    && (forall x₁₀: int ::
                                                          (x₁₀ != 0
                                                             ==> sum[0 := 0][x₁₀] == sum[0 := 0][x₁₀]))
                                                    && (forall i₉: int ::
                                                          (  i₉ <= i₉
                                                            && 0 <= i₉
                                                            && i₉ < 0
                                                             ==> i₉ < N₁₉))
                                                    && (forall sum₂₂: [int]int, i₂₃: int ::
                                                          (  true
                                                            && 0 <= i₂₃
                                                            && i₂₃ <= N₁₉
                                                            && (forall x₁₀: int ::
                                                                  (x₁₀ == 0
                                                                     ==> (exists i₉: int ::
                                                                            i₉ < N₁₉
                                                                            && x₁₀ == 0
                                                                            && sum₂₂[x₁₀] == a₂₀[i₉] + sum[0 := 0][0])))
                                                            && (forall x₁₀: int ::
                                                                  (x₁₀ != 0
                                                                     ==> sum₂₂[x₁₀] == sum[0 := 0][x₁₀]))
                                                            && (forall i₉: int ::
                                                                  (  i₉ <= i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₂₃
                                                                     ==> i₉ < N₁₉))
                                                             ==> (i₂₃ < N₁₉
                                                                 ==> true
                                                                  && 0 <= i₂₃ + 1
                                                                  && i₂₃ + 1 <= N₁₉
                                                                  && (forall x₁₀: int ::
                                                                        (x₁₀ == 0
                                                                           ==> (exists i₉: int ::
                                                                                  i₉ < N₁₉
                                                                                  && x₁₀ == 0
                                                                                  && sum₂₂[0 := sum₂₂[0] + a₂₀[i₂₃]][x₁₀] == a₂₀[i₉] + sum[0 := 0][0])))
                                                                  && (forall x₁₀: int ::
                                                                        (x₁₀ != 0
                                                                           ==> sum₂₂[0 := sum₂₂[0] + a₂₀[i₂₃]][x₁₀] == sum[0 := 0][x₁₀]))
                                                                  && (forall i₉: int ::
                                                                        (  i₉ <= i₉
                                                                          && 0 <= i₉
                                                                          && i₉ < i₂₃ + 1
                                                                           ==> i₉ < N₁₉))
                                                                  && true
                                                                  && (true
                                                                     ==> true))
                                                              && (!(i₂₃ < N₁₉
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> true
                                                                      && 0 <= 0
                                                                      && 0 <= N₁₉
                                                                      && (forall x₁₄: int ::
                                                                            ((exists i₁₃: int ::
                                                                                    x₁₄ == i₁₃
                                                                                    && 0 <= i₁₃
                                                                                    && i₁₃ < 0)
                                                                               ==> (exists i₁₃: int ::
                                                                                      i₁₃ < N₁₉
                                                                                      && x₁₄ == i₁₃
                                                                                      && 0 <= i₁₃
                                                                                      && i₁₃ < 0
                                                                                      && a₂₀[x₁₄] == sum₂₂[0] + a₂₀[i₁₃])))
                                                                      && (forall x₁₄: int ::
                                                                            (!((exists i₁₃: int ::
                                                                                    x₁₄ == i₁₃
                                                                                    && 0 <= i₁₃
                                                                                    && i₁₃ < 0)
                                                                            )
                                                                               ==> a₂₀[x₁₄] == a₂₀[x₁₄]))
                                                                      && (forall i₁₃: int ::
                                                                            (  i₁₃ <= i₁₃
                                                                              && 0 <= i₁₃
                                                                              && i₁₃ < 0
                                                                               ==> i₁₃ < N₁₉))
                                                                      && (forall a₂₄: [int]int, i₂₅: int ::
                                                                            (  true
                                                                              && 0 <= i₂₅
                                                                              && i₂₅ <= N₁₉
                                                                              && (forall x₁₄: int ::
                                                                                    ((exists i₁₃: int ::
                                                                                            x₁₄ == i₁₃
                                                                                            && 0 <= i₁₃
                                                                                            && i₁₃ < i₂₅)
                                                                                       ==> (exists i₁₃: int ::
                                                                                              i₁₃ < N₁₉
                                                                                              && x₁₄ == i₁₃
                                                                                              && 0 <= i₁₃
                                                                                              && i₁₃ < i₂₅
                                                                                              && a₂₄[x₁₄] == sum₂₂[0] + a₂₀[i₁₃])))
                                                                              && (forall x₁₄: int ::
                                                                                    (!((exists i₁₃: int ::
                                                                                            x₁₄ == i₁₃
                                                                                            && 0 <= i₁₃
                                                                                            && i₁₃ < i₂₅)
                                                                                    )
                                                                                       ==> a₂₄[x₁₄] == a₂₀[x₁₄]))
                                                                              && (forall i₁₃: int ::
                                                                                    (  i₁₃ <= i₁₃
                                                                                      && 0 <= i₁₃
                                                                                      && i₁₃ < i₂₅
                                                                                       ==> i₁₃ < N₁₉))
                                                                               ==> (i₂₅ < N₁₉
                                                                                   ==> true
                                                                                    && 0 <= i₂₅ + 1
                                                                                    && i₂₅ + 1 <= N₁₉
                                                                                    && (forall x₁₄: int ::
                                                                                          ((exists i₁₃: int ::
                                                                                                  x₁₄ == i₁₃
                                                                                                  && 0 <= i₁₃
                                                                                                  && i₁₃ < i₂₅ + 1)
                                                                                             ==> (exists i₁₃: int ::
                                                                                                    i₁₃ < N₁₉
                                                                                                    && x₁₄ == i₁₃
                                                                                                    && 0 <= i₁₃
                                                                                                    && i₁₃ < i₂₅ + 1
                                                                                                    && a₂₄[i₂₅ := a₂₄[i₂₅] + sum₂₂[0]][x₁₄] == sum₂₂[0] + a₂₀[i₁₃])))
                                                                                    && (forall x₁₄: int ::
                                                                                          (!((exists i₁₃: int ::
                                                                                                  x₁₄ == i₁₃
                                                                                                  && 0 <= i₁₃
                                                                                                  && i₁₃ < i₂₅ + 1)
                                                                                          )
                                                                                             ==> a₂₄[i₂₅ := a₂₄[i₂₅] + sum₂₂[0]][x₁₄] == a₂₀[x₁₄]))
                                                                                    && (forall i₁₃: int ::
                                                                                          (  i₁₃ <= i₁₃
                                                                                            && 0 <= i₁₃
                                                                                            && i₁₃ < i₂₅ + 1
                                                                                             ==> i₁₃ < N₁₉))
                                                                                    && true
                                                                                    && (true
                                                                                       ==> true))
                                                                                && (!(i₂₅ < N₁₉
                                                                                )
                                                                                   ==> true
                                                                                    && (true
                                                                                       ==> true
                                                                                        && 0 <= 0
                                                                                        && 0 <= N₁₉
                                                                                        && (forall i₁₇: int ::
                                                                                              (  i₁₇ <= i₁₇
                                                                                                && 0 <= i₁₇
                                                                                                && i₁₇ < 0
                                                                                                 ==> i₁₇ < N₁₉))
                                                                                        && (forall i₂₆: int ::
                                                                                              (  true
                                                                                                && 0 <= i₂₆
                                                                                                && i₂₆ <= N₁₉
                                                                                                && (forall i₁₇: int ::
                                                                                                      (  i₁₇ <= i₁₇
                                                                                                        && 0 <= i₁₇
                                                                                                        && i₁₇ < i₂₆
                                                                                                         ==> i₁₇ < N₁₉))
                                                                                                 ==> (i₂₆ < N₁₉
                                                                                                     ==> a₂₄[i₂₆] == N₁₉ + 1
                                                                                                      && (true
                                                                                                         ==> true
                                                                                                          && 0 <= i₂₆ + 1
                                                                                                          && i₂₆ + 1 <= N₁₉
                                                                                                          && (forall i₁₇: int ::
                                                                                                                (  i₁₇ <= i₁₇
                                                                                                                  && 0 <= i₁₇
                                                                                                                  && i₁₇ < i₂₆ + 1
                                                                                                                   ==> i₁₇ < N₁₉))
                                                                                                          && true
                                                                                                          && (true
                                                                                                             ==> true)))
                                                                                                  && (!(i₂₆ < N₁₉
                                                                                                  )
                                                                                                     ==> true
                                                                                                      && (true
                                                                                                         ==> true)))))))))))))))))))))));


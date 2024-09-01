data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall N₁₃: int ::
          (true
             ==> (N₁₃ <= 0
                 ==> true)
              && (!(N₁₃ <= 0
              )
                 ==> true
                  && (N₁₃ <= 2147483647 / 4
                     ==> (forall sum: [int]int ::
                          (forall a: [int]int ::
                                  true
                                  && 0 <= 0
                                  && 0 <= N₁₃
                                  && (forall x₆: int ::
                                        ((exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < 0)
                                           ==> (exists i₅: int ::
                                                  i₅ < N₁₃
                                                  && x₆ == i₅
                                                  && 0 <= i₅
                                                  && i₅ < 0
                                                  && a[x₆] == i₅ % 1)))
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
                                           ==> i₅ < N₁₃))
                                  && (forall a₁₄: [int]int, i₁₅: int ::
                                        (  true
                                          && 0 <= i₁₅
                                          && i₁₅ <= N₁₃
                                          && (forall x₆: int ::
                                                ((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₁₅)
                                                   ==> (exists i₅: int ::
                                                          i₅ < N₁₃
                                                          && x₆ == i₅
                                                          && 0 <= i₅
                                                          && i₅ < i₁₅
                                                          && a₁₄[x₆] == i₅ % 1)))
                                          && (forall x₆: int ::
                                                (!((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₁₅)
                                                )
                                                   ==> a₁₄[x₆] == a[x₆]))
                                          && (forall i₅: int ::
                                                (  i₅ <= i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₁₅
                                                   ==> i₅ < N₁₃))
                                           ==> (i₁₅ < N₁₃
                                               ==> true
                                                && 0 <= i₁₅ + 1
                                                && i₁₅ + 1 <= N₁₃
                                                && (forall x₆: int ::
                                                      ((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 0 <= i₅
                                                              && i₅ < i₁₅ + 1)
                                                         ==> (exists i₅: int ::
                                                                i₅ < N₁₃
                                                                && x₆ == i₅
                                                                && 0 <= i₅
                                                                && i₅ < i₁₅ + 1
                                                                && a₁₄[i₁₅ := i₁₅ % 1][x₆] == i₅ % 1)))
                                                && (forall x₆: int ::
                                                      (!((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 0 <= i₅
                                                              && i₅ < i₁₅ + 1)
                                                      )
                                                         ==> a₁₄[i₁₅ := i₁₅ % 1][x₆] == a[x₆]))
                                                && (forall i₅: int ::
                                                      (  i₅ <= i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₁₅ + 1
                                                         ==> i₅ < N₁₃))
                                                && true
                                                && (true
                                                   ==> true))
                                            && (!(i₁₅ < N₁₃
                                            )
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 0 <= 0
                                                    && 0 <= N₁₃
                                                    && (forall x₁₀: int ::
                                                          (x₁₀ == 0
                                                             ==> (exists i₉: int ::
                                                                      i₉ == 0
                                                                      && i₉ < N₁₃
                                                                      && x₁₀ == 0
                                                                      && sum[x₁₀] == 0)
                                                              || (exists i₉: int ::
                                                                      i₉ != 0
                                                                      && i₉ < N₁₃
                                                                      && x₁₀ == 0
                                                                      && sum[x₁₀] == a₁₄[i₉] + sum[0])))
                                                    && (forall x₁₀: int ::
                                                          (x₁₀ != 0
                                                             ==> sum[x₁₀] == sum[x₁₀]))
                                                    && (forall i₉: int ::
                                                          (  i₉ <= i₉
                                                            && 0 <= i₉
                                                            && i₉ < 0
                                                             ==> i₉ < N₁₃))
                                                    && (forall sum₁₆: [int]int, i₁₇: int ::
                                                          (  true
                                                            && 0 <= i₁₇
                                                            && i₁₇ <= N₁₃
                                                            && (forall x₁₀: int ::
                                                                  (x₁₀ == 0
                                                                     ==> (exists i₉: int ::
                                                                              i₉ == 0
                                                                              && i₉ < N₁₃
                                                                              && x₁₀ == 0
                                                                              && sum₁₆[x₁₀] == 0)
                                                                      || (exists i₉: int ::
                                                                              i₉ != 0
                                                                              && i₉ < N₁₃
                                                                              && x₁₀ == 0
                                                                              && sum₁₆[x₁₀] == a₁₄[i₉] + sum[0])))
                                                            && (forall x₁₀: int ::
                                                                  (x₁₀ != 0
                                                                     ==> sum₁₆[x₁₀] == sum[x₁₀]))
                                                            && (forall i₉: int ::
                                                                  (  i₉ <= i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₁₇
                                                                     ==> i₉ < N₁₃))
                                                             ==> (i₁₇ < N₁₃
                                                                 ==> (i₁₇ == 0
                                                                     ==> true
                                                                      && 0 <= i₁₇ + 1
                                                                      && i₁₇ + 1 <= N₁₃
                                                                      && (forall x₁₀: int ::
                                                                            (x₁₀ == 0
                                                                               ==> (exists i₉: int ::
                                                                                        i₉ == 0
                                                                                        && i₉ < N₁₃
                                                                                        && x₁₀ == 0
                                                                                        && sum₁₆[0 := 0][x₁₀] == 0)
                                                                                || (exists i₉: int ::
                                                                                        i₉ != 0
                                                                                        && i₉ < N₁₃
                                                                                        && x₁₀ == 0
                                                                                        && sum₁₆[0 := 0][x₁₀] == a₁₄[i₉] + sum[0])))
                                                                      && (forall x₁₀: int ::
                                                                            (x₁₀ != 0
                                                                               ==> sum₁₆[0 := 0][x₁₀] == sum[x₁₀]))
                                                                      && (forall i₉: int ::
                                                                            (  i₉ <= i₉
                                                                              && 0 <= i₉
                                                                              && i₉ < i₁₇ + 1
                                                                               ==> i₉ < N₁₃))
                                                                      && true
                                                                      && (true
                                                                         ==> true))
                                                                  && (i₁₇ != 0
                                                                     ==> true
                                                                      && 0 <= i₁₇ + 1
                                                                      && i₁₇ + 1 <= N₁₃
                                                                      && (forall x₁₀: int ::
                                                                            (x₁₀ == 0
                                                                               ==> (exists i₉: int ::
                                                                                        i₉ == 0
                                                                                        && i₉ < N₁₃
                                                                                        && x₁₀ == 0
                                                                                        && sum₁₆[0 := sum₁₆[0] + a₁₄[i₁₇]][x₁₀] == 0)
                                                                                || (exists i₉: int ::
                                                                                        i₉ != 0
                                                                                        && i₉ < N₁₃
                                                                                        && x₁₀ == 0
                                                                                        && sum₁₆[0 := sum₁₆[0] + a₁₄[i₁₇]][x₁₀] == a₁₄[i₉] + sum[0])))
                                                                      && (forall x₁₀: int ::
                                                                            (x₁₀ != 0
                                                                               ==> sum₁₆[0 := sum₁₆[0] + a₁₄[i₁₇]][x₁₀] == sum[x₁₀]))
                                                                      && (forall i₉: int ::
                                                                            (  i₉ <= i₉
                                                                              && 0 <= i₉
                                                                              && i₉ < i₁₇ + 1
                                                                               ==> i₉ < N₁₃))
                                                                      && true
                                                                      && (true
                                                                         ==> true)))
                                                              && (!(i₁₇ < N₁₃
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> sum₁₆[0] == 0
                                                                      && (true
                                                                         ==> true))))))))))))))));


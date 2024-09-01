data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall N₂₃: int ::
          (true
             ==> (N₂₃ <= 0
                 ==> true)
              && (!(N₂₃ <= 0
              )
                 ==> true
                  && (N₂₃ <= 2147483647 / 4
                     ==> (forall sum: [int]int ::
                          (forall a: [int]int ::
                                  true
                                  && 0 <= 0
                                  && 0 <= N₂₃
                                  && (forall x₆: int ::
                                        ((exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < 0)
                                           ==> (exists i₅: int ::
                                                  i₅ < N₂₃
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
                                           ==> i₅ < N₂₃))
                                  && (forall a₂₄: [int]int, i₂₅: int ::
                                        (  true
                                          && 0 <= i₂₅
                                          && i₂₅ <= N₂₃
                                          && (forall x₆: int ::
                                                ((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₂₅)
                                                   ==> (exists i₅: int ::
                                                          i₅ < N₂₃
                                                          && x₆ == i₅
                                                          && 0 <= i₅
                                                          && i₅ < i₂₅
                                                          && a₂₄[x₆] == 1)))
                                          && (forall x₆: int ::
                                                (!((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₂₅)
                                                )
                                                   ==> a₂₄[x₆] == a[x₆]))
                                          && (forall i₅: int ::
                                                (  i₅ <= i₅
                                                  && 0 <= i₅
                                                  && i₅ < i₂₅
                                                   ==> i₅ < N₂₃))
                                           ==> (i₂₅ < N₂₃
                                               ==> true
                                                && 0 <= i₂₅ + 1
                                                && i₂₅ + 1 <= N₂₃
                                                && (forall x₆: int ::
                                                      ((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 0 <= i₅
                                                              && i₅ < i₂₅ + 1)
                                                         ==> (exists i₅: int ::
                                                                i₅ < N₂₃
                                                                && x₆ == i₅
                                                                && 0 <= i₅
                                                                && i₅ < i₂₅ + 1
                                                                && a₂₄[i₂₅ := 1][x₆] == 1)))
                                                && (forall x₆: int ::
                                                      (!((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 0 <= i₅
                                                              && i₅ < i₂₅ + 1)
                                                      )
                                                         ==> a₂₄[i₂₅ := 1][x₆] == a[x₆]))
                                                && (forall i₅: int ::
                                                      (  i₅ <= i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₂₅ + 1
                                                         ==> i₅ < N₂₃))
                                                && true
                                                && (true
                                                   ==> true))
                                            && (!(i₂₅ < N₂₃
                                            )
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 0 <= 0
                                                    && 0 <= N₂₃
                                                    && (forall x₁₀: int ::
                                                          (x₁₀ == 0
                                                             ==> (exists i₉: int ::
                                                                    i₉ < N₂₃
                                                                    && x₁₀ == 0
                                                                    && sum[0 := 0][x₁₀] == a₂₄[i₉] + sum[0 := 0][0])))
                                                    && (forall x₁₀: int ::
                                                          (x₁₀ != 0
                                                             ==> sum[0 := 0][x₁₀] == sum[0 := 0][x₁₀]))
                                                    && (forall i₉: int ::
                                                          (  i₉ <= i₉
                                                            && 0 <= i₉
                                                            && i₉ < 0
                                                             ==> i₉ < N₂₃))
                                                    && (forall sum₂₆: [int]int, i₂₇: int ::
                                                          (  true
                                                            && 0 <= i₂₇
                                                            && i₂₇ <= N₂₃
                                                            && (forall x₁₀: int ::
                                                                  (x₁₀ == 0
                                                                     ==> (exists i₉: int ::
                                                                            i₉ < N₂₃
                                                                            && x₁₀ == 0
                                                                            && sum₂₆[x₁₀] == a₂₄[i₉] + sum[0 := 0][0])))
                                                            && (forall x₁₀: int ::
                                                                  (x₁₀ != 0
                                                                     ==> sum₂₆[x₁₀] == sum[0 := 0][x₁₀]))
                                                            && (forall i₉: int ::
                                                                  (  i₉ <= i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₂₇
                                                                     ==> i₉ < N₂₃))
                                                             ==> (i₂₇ < N₂₃
                                                                 ==> true
                                                                  && 0 <= i₂₇ + 1
                                                                  && i₂₇ + 1 <= N₂₃
                                                                  && (forall x₁₀: int ::
                                                                        (x₁₀ == 0
                                                                           ==> (exists i₉: int ::
                                                                                  i₉ < N₂₃
                                                                                  && x₁₀ == 0
                                                                                  && sum₂₆[0 := sum₂₆[0] + a₂₄[i₂₇]][x₁₀] == a₂₄[i₉] + sum[0 := 0][0])))
                                                                  && (forall x₁₀: int ::
                                                                        (x₁₀ != 0
                                                                           ==> sum₂₆[0 := sum₂₆[0] + a₂₄[i₂₇]][x₁₀] == sum[0 := 0][x₁₀]))
                                                                  && (forall i₉: int ::
                                                                        (  i₉ <= i₉
                                                                          && 0 <= i₉
                                                                          && i₉ < i₂₇ + 1
                                                                           ==> i₉ < N₂₃))
                                                                  && true
                                                                  && (true
                                                                     ==> true))
                                                              && (!(i₂₇ < N₂₃
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> true
                                                                      && 0 <= 0
                                                                      && 0 <= N₂₃
                                                                      && (forall x₁₄: int ::
                                                                            ((exists i₁₃: int ::
                                                                                    x₁₄ == i₁₃
                                                                                    && 0 <= i₁₃
                                                                                    && i₁₃ < 0)
                                                                               ==> (exists i₁₃: int ::
                                                                                      i₁₃ < N₂₃
                                                                                      && x₁₄ == i₁₃
                                                                                      && 0 <= i₁₃
                                                                                      && i₁₃ < 0
                                                                                      && a₂₄[x₁₄] == sum₂₆[0] + a₂₄[i₁₃])))
                                                                      && (forall x₁₄: int ::
                                                                            (!((exists i₁₃: int ::
                                                                                    x₁₄ == i₁₃
                                                                                    && 0 <= i₁₃
                                                                                    && i₁₃ < 0)
                                                                            )
                                                                               ==> a₂₄[x₁₄] == a₂₄[x₁₄]))
                                                                      && (forall i₁₃: int ::
                                                                            (  i₁₃ <= i₁₃
                                                                              && 0 <= i₁₃
                                                                              && i₁₃ < 0
                                                                               ==> i₁₃ < N₂₃))
                                                                      && (forall a₂₈: [int]int, i₂₉: int ::
                                                                            (  true
                                                                              && 0 <= i₂₉
                                                                              && i₂₉ <= N₂₃
                                                                              && (forall x₁₄: int ::
                                                                                    ((exists i₁₃: int ::
                                                                                            x₁₄ == i₁₃
                                                                                            && 0 <= i₁₃
                                                                                            && i₁₃ < i₂₉)
                                                                                       ==> (exists i₁₃: int ::
                                                                                              i₁₃ < N₂₃
                                                                                              && x₁₄ == i₁₃
                                                                                              && 0 <= i₁₃
                                                                                              && i₁₃ < i₂₉
                                                                                              && a₂₈[x₁₄] == sum₂₆[0] + a₂₄[i₁₃])))
                                                                              && (forall x₁₄: int ::
                                                                                    (!((exists i₁₃: int ::
                                                                                            x₁₄ == i₁₃
                                                                                            && 0 <= i₁₃
                                                                                            && i₁₃ < i₂₉)
                                                                                    )
                                                                                       ==> a₂₈[x₁₄] == a₂₄[x₁₄]))
                                                                              && (forall i₁₃: int ::
                                                                                    (  i₁₃ <= i₁₃
                                                                                      && 0 <= i₁₃
                                                                                      && i₁₃ < i₂₉
                                                                                       ==> i₁₃ < N₂₃))
                                                                               ==> (i₂₉ < N₂₃
                                                                                   ==> true
                                                                                    && 0 <= i₂₉ + 1
                                                                                    && i₂₉ + 1 <= N₂₃
                                                                                    && (forall x₁₄: int ::
                                                                                          ((exists i₁₃: int ::
                                                                                                  x₁₄ == i₁₃
                                                                                                  && 0 <= i₁₃
                                                                                                  && i₁₃ < i₂₉ + 1)
                                                                                             ==> (exists i₁₃: int ::
                                                                                                    i₁₃ < N₂₃
                                                                                                    && x₁₄ == i₁₃
                                                                                                    && 0 <= i₁₃
                                                                                                    && i₁₃ < i₂₉ + 1
                                                                                                    && a₂₈[i₂₉ := a₂₈[i₂₉] + sum₂₆[0]][x₁₄] == sum₂₆[0] + a₂₄[i₁₃])))
                                                                                    && (forall x₁₄: int ::
                                                                                          (!((exists i₁₃: int ::
                                                                                                  x₁₄ == i₁₃
                                                                                                  && 0 <= i₁₃
                                                                                                  && i₁₃ < i₂₉ + 1)
                                                                                          )
                                                                                             ==> a₂₈[i₂₉ := a₂₈[i₂₉] + sum₂₆[0]][x₁₄] == a₂₄[x₁₄]))
                                                                                    && (forall i₁₃: int ::
                                                                                          (  i₁₃ <= i₁₃
                                                                                            && 0 <= i₁₃
                                                                                            && i₁₃ < i₂₉ + 1
                                                                                             ==> i₁₃ < N₂₃))
                                                                                    && true
                                                                                    && (true
                                                                                       ==> true))
                                                                                && (!(i₂₉ < N₂₃
                                                                                )
                                                                                   ==> true
                                                                                    && (true
                                                                                       ==> true
                                                                                        && 0 <= 0
                                                                                        && 0 <= N₂₃
                                                                                        && (forall x₁₈: int ::
                                                                                              ((exists i₁₇: int ::
                                                                                                      x₁₈ == i₁₇
                                                                                                      && 0 <= i₁₇
                                                                                                      && i₁₇ < 0)
                                                                                                 ==> (exists i₁₇: int ::
                                                                                                        i₁₇ < N₂₃
                                                                                                        && x₁₈ == i₁₇
                                                                                                        && 0 <= i₁₇
                                                                                                        && i₁₇ < 0
                                                                                                        && a₂₈[x₁₈] == a₂₈[i₁₇] % (1 + sum₂₆[0]))))
                                                                                        && (forall x₁₈: int ::
                                                                                              (!((exists i₁₇: int ::
                                                                                                      x₁₈ == i₁₇
                                                                                                      && 0 <= i₁₇
                                                                                                      && i₁₇ < 0)
                                                                                              )
                                                                                                 ==> a₂₈[x₁₈] == a₂₈[x₁₈]))
                                                                                        && (forall i₁₇: int ::
                                                                                              (  i₁₇ <= i₁₇
                                                                                                && 0 <= i₁₇
                                                                                                && i₁₇ < 0
                                                                                                 ==> i₁₇ < N₂₃))
                                                                                        && (forall a₃₀: [int]int, i₃₁: int ::
                                                                                              (  true
                                                                                                && 0 <= i₃₁
                                                                                                && i₃₁ <= N₂₃
                                                                                                && (forall x₁₈: int ::
                                                                                                      ((exists i₁₇: int ::
                                                                                                              x₁₈ == i₁₇
                                                                                                              && 0 <= i₁₇
                                                                                                              && i₁₇ < i₃₁)
                                                                                                         ==> (exists i₁₇: int ::
                                                                                                                i₁₇ < N₂₃
                                                                                                                && x₁₈ == i₁₇
                                                                                                                && 0 <= i₁₇
                                                                                                                && i₁₇ < i₃₁
                                                                                                                && a₃₀[x₁₈] == a₂₈[i₁₇] % (1 + sum₂₆[0]))))
                                                                                                && (forall x₁₈: int ::
                                                                                                      (!((exists i₁₇: int ::
                                                                                                              x₁₈ == i₁₇
                                                                                                              && 0 <= i₁₇
                                                                                                              && i₁₇ < i₃₁)
                                                                                                      )
                                                                                                         ==> a₃₀[x₁₈] == a₂₈[x₁₈]))
                                                                                                && (forall i₁₇: int ::
                                                                                                      (  i₁₇ <= i₁₇
                                                                                                        && 0 <= i₁₇
                                                                                                        && i₁₇ < i₃₁
                                                                                                         ==> i₁₇ < N₂₃))
                                                                                                 ==> (i₃₁ < N₂₃
                                                                                                     ==> true
                                                                                                      && 0 <= i₃₁ + 1
                                                                                                      && i₃₁ + 1 <= N₂₃
                                                                                                      && (forall x₁₈: int ::
                                                                                                            ((exists i₁₇: int ::
                                                                                                                    x₁₈ == i₁₇
                                                                                                                    && 0 <= i₁₇
                                                                                                                    && i₁₇ < i₃₁ + 1)
                                                                                                               ==> (exists i₁₇: int ::
                                                                                                                      i₁₇ < N₂₃
                                                                                                                      && x₁₈ == i₁₇
                                                                                                                      && 0 <= i₁₇
                                                                                                                      && i₁₇ < i₃₁ + 1
                                                                                                                      && a₃₀[i₃₁ := a₃₀[i₃₁] % (sum₂₆[0] + 1)][x₁₈] == a₂₈[i₁₇] % (1 + sum₂₆[0]))))
                                                                                                      && (forall x₁₈: int ::
                                                                                                            (!((exists i₁₇: int ::
                                                                                                                    x₁₈ == i₁₇
                                                                                                                    && 0 <= i₁₇
                                                                                                                    && i₁₇ < i₃₁ + 1)
                                                                                                            )
                                                                                                               ==> a₃₀[i₃₁ := a₃₀[i₃₁] % (sum₂₆[0] + 1)][x₁₈] == a₂₈[x₁₈]))
                                                                                                      && (forall i₁₇: int ::
                                                                                                            (  i₁₇ <= i₁₇
                                                                                                              && 0 <= i₁₇
                                                                                                              && i₁₇ < i₃₁ + 1
                                                                                                               ==> i₁₇ < N₂₃))
                                                                                                      && true
                                                                                                      && (true
                                                                                                         ==> true))
                                                                                                  && (!(i₃₁ < N₂₃
                                                                                                  )
                                                                                                     ==> true
                                                                                                      && (true
                                                                                                         ==> true
                                                                                                          && 0 <= 0
                                                                                                          && 0 <= N₂₃
                                                                                                          && (forall i₂₁: int ::
                                                                                                                (  i₂₁ <= i₂₁
                                                                                                                  && 0 <= i₂₁
                                                                                                                  && i₂₁ < 0
                                                                                                                   ==> i₂₁ < N₂₃))
                                                                                                          && (forall i₃₂: int ::
                                                                                                                (  true
                                                                                                                  && 0 <= i₃₂
                                                                                                                  && i₃₂ <= N₂₃
                                                                                                                  && (forall i₂₁: int ::
                                                                                                                        (  i₂₁ <= i₂₁
                                                                                                                          && 0 <= i₂₁
                                                                                                                          && i₂₁ < i₃₂
                                                                                                                           ==> i₂₁ < N₂₃))
                                                                                                                   ==> (i₃₂ < N₂₃
                                                                                                                       ==> a₃₀[i₃₂] == 0
                                                                                                                        && (true
                                                                                                                           ==> true
                                                                                                                            && 0 <= i₃₂ + 1
                                                                                                                            && i₃₂ + 1 <= N₂₃
                                                                                                                            && (forall i₂₁: int ::
                                                                                                                                  (  i₂₁ <= i₂₁
                                                                                                                                    && 0 <= i₂₁
                                                                                                                                    && i₂₁ < i₃₂ + 1
                                                                                                                                     ==> i₂₁ < N₂₃))
                                                                                                                            && true
                                                                                                                            && (true
                                                                                                                               ==> true)))
                                                                                                                    && (!(i₃₂ < N₂₃
                                                                                                                    )
                                                                                                                       ==> true
                                                                                                                        && (true
                                                                                                                           ==> true)))))))))))))))))))))))))));


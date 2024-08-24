data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₇: int ::
        N₂₇ <= 0
        || (forall sum: [int]int, a: [int]int ::
              (N₂₇ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₂₇
                  && (forall x₆: int, i₅: int ::
                        (  x₆ == i₅
                          && 0 <= i₅
                          && i₅ < 0
                           ==> (exists i₅: int ::
                                  i₅ < N₂₇
                                  && x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0
                                  && a[x₆] == 1)))
                  && (forall x₆: int ::
                          (exists i₅: int ::
                                  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                          || a[x₆] == a[x₆])
                  && (forall i₅: int ::
                        (  0 <= i₅
                          && i₅ < 0
                           ==> i₅ < N₂₇))
                  && (forall a₂₈: [int]int, i₂₉: int ::
                        (  0 <= i₂₉
                          && i₂₉ <= N₂₇
                          && (forall x₆: int, i₅: int ::
                                (  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < i₂₉
                                   ==> (exists i₅: int ::
                                          i₅ < N₂₇
                                          && x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₉
                                          && a₂₈[x₆] == 1)))
                          && (forall x₆: int ::
                                  (exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₉)
                                  || a₂₈[x₆] == a[x₆])
                          && (forall i₅: int ::
                                (  0 <= i₅
                                  && i₅ < i₂₉
                                   ==> i₅ < N₂₇))
                           ==> (i₂₉ < N₂₇
                               ==> 0 <= i₂₉ + 1
                                && i₂₉ + 1 <= N₂₇
                                && (forall x₆: int, i₅: int ::
                                      (  x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₂₉ + 1
                                         ==> (exists i₅: int ::
                                                i₅ < N₂₇
                                                && x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₉ + 1
                                                && a₂₈[i₂₉ := 1][x₆] == 1)))
                                && (forall x₆: int ::
                                        (exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₉ + 1)
                                        || a₂₈[i₂₉ := 1][x₆] == a[x₆])
                                && (forall i₅: int ::
                                      (  0 <= i₅
                                        && i₅ < i₂₉ + 1
                                         ==> i₅ < N₂₇)))
                            &&   i₂₉ < N₂₇
                              ||   0 <= 0
                                && 0 <= N₂₇
                                && (forall x₁₀: int ::
                                      (x₁₀ == 0
                                         ==> (exists i₉: int ::
                                                i₉ < N₂₇
                                                && x₁₀ == 0
                                                && sum[0 := 0][x₁₀] == sum[0 := 0][0] + a₂₈[i₉])))
                                && (forall x₁₀: int ::
                                        x₁₀ == 0
                                        || sum[0 := 0][x₁₀] == sum[0 := 0][x₁₀])
                                && (forall i₉: int ::
                                      (  0 <= i₉
                                        && i₉ < 0
                                         ==> i₉ < N₂₇))
                                && (forall sum₃₀: [int]int, i₃₁: int ::
                                      (  0 <= i₃₁
                                        && i₃₁ <= N₂₇
                                        && (forall x₁₀: int ::
                                              (x₁₀ == 0
                                                 ==> (exists i₉: int ::
                                                        i₉ < N₂₇
                                                        && x₁₀ == 0
                                                        && sum₃₀[x₁₀] == sum[0 := 0][0] + a₂₈[i₉])))
                                        && (forall x₁₀: int ::
                                                x₁₀ == 0
                                                || sum₃₀[x₁₀] == sum[0 := 0][x₁₀])
                                        && (forall i₉: int ::
                                              (  0 <= i₉
                                                && i₉ < i₃₁
                                                 ==> i₉ < N₂₇))
                                         ==> (i₃₁ < N₂₇
                                             ==> 0 <= i₃₁ + 1
                                              && i₃₁ + 1 <= N₂₇
                                              && (forall x₁₀: int ::
                                                    (x₁₀ == 0
                                                       ==> (exists i₉: int ::
                                                              i₉ < N₂₇
                                                              && x₁₀ == 0
                                                              && sum₃₀[0 := sum₃₀[0] + a₂₈[i₃₁]][x₁₀] == sum[0 := 0][0] + a₂₈[i₉])))
                                              && (forall x₁₀: int ::
                                                      x₁₀ == 0
                                                      || sum₃₀[0 := sum₃₀[0] + a₂₈[i₃₁]][x₁₀] == sum[0 := 0][x₁₀])
                                              && (forall i₉: int ::
                                                    (  0 <= i₉
                                                      && i₉ < i₃₁ + 1
                                                       ==> i₉ < N₂₇)))
                                          &&   i₃₁ < N₂₇
                                            ||   0 <= 0
                                              && 0 <= N₂₇
                                              && (forall x₁₄: int, i₁₃: int ::
                                                    (  x₁₄ == i₁₃
                                                      && 0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> (exists i₁₃: int ::
                                                              i₁₃ < N₂₇
                                                              && x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < 0
                                                              && a₂₈[x₁₄] == sum₃₀[0] + a₂₈[i₁₃])))
                                              && (forall x₁₄: int ::
                                                      (exists i₁₃: int ::
                                                              x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < 0)
                                                      || a₂₈[x₁₄] == a₂₈[x₁₄])
                                              && (forall i₁₃: int ::
                                                    (  0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> i₁₃ < N₂₇))
                                              && (forall a₃₂: [int]int, i₃₃: int ::
                                                    (  0 <= i₃₃
                                                      && i₃₃ <= N₂₇
                                                      && (forall x₁₄: int, i₁₃: int ::
                                                            (  x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < i₃₃
                                                               ==> (exists i₁₃: int ::
                                                                      i₁₃ < N₂₇
                                                                      && x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₃₃
                                                                      && a₃₂[x₁₄] == sum₃₀[0] + a₂₈[i₁₃])))
                                                      && (forall x₁₄: int ::
                                                              (exists i₁₃: int ::
                                                                      x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₃₃)
                                                              || a₃₂[x₁₄] == a₂₈[x₁₄])
                                                      && (forall i₁₃: int ::
                                                            (  0 <= i₁₃
                                                              && i₁₃ < i₃₃
                                                               ==> i₁₃ < N₂₇))
                                                       ==> (i₃₃ < N₂₇
                                                           ==> 0 <= i₃₃ + 1
                                                            && i₃₃ + 1 <= N₂₇
                                                            && (forall x₁₄: int, i₁₃: int ::
                                                                  (  x₁₄ == i₁₃
                                                                    && 0 <= i₁₃
                                                                    && i₁₃ < i₃₃ + 1
                                                                     ==> (exists i₁₃: int ::
                                                                            i₁₃ < N₂₇
                                                                            && x₁₄ == i₁₃
                                                                            && 0 <= i₁₃
                                                                            && i₁₃ < i₃₃ + 1
                                                                            && a₃₂[i₃₃ := a₃₂[i₃₃] + sum₃₀[0]][x₁₄] == sum₃₀[0] + a₂₈[i₁₃])))
                                                            && (forall x₁₄: int ::
                                                                    (exists i₁₃: int ::
                                                                            x₁₄ == i₁₃
                                                                            && 0 <= i₁₃
                                                                            && i₁₃ < i₃₃ + 1)
                                                                    || a₃₂[i₃₃ := a₃₂[i₃₃] + sum₃₀[0]][x₁₄] == a₂₈[x₁₄])
                                                            && (forall i₁₃: int ::
                                                                  (  0 <= i₁₃
                                                                    && i₁₃ < i₃₃ + 1
                                                                     ==> i₁₃ < N₂₇)))
                                                        &&   i₃₃ < N₂₇
                                                          ||   0 <= 0
                                                            && 0 <= N₂₇
                                                            && (forall x₁₈: int ::
                                                                  (x₁₈ == 0
                                                                     ==> (exists i₁₇: int ::
                                                                            i₁₇ < N₂₇
                                                                            && x₁₈ == 0
                                                                            && sum₃₀[0 := 1][x₁₈] == a₃₂[i₁₇] + sum₃₀[0 := 1][0])))
                                                            && (forall x₁₈: int ::
                                                                    x₁₈ == 0
                                                                    || sum₃₀[0 := 1][x₁₈] == sum₃₀[0 := 1][x₁₈])
                                                            && (forall i₁₇: int ::
                                                                  (  0 <= i₁₇
                                                                    && i₁₇ < 0
                                                                     ==> i₁₇ < N₂₇))
                                                            && (forall sum₃₄: [int]int, i₃₅: int ::
                                                                  (  0 <= i₃₅
                                                                    && i₃₅ <= N₂₇
                                                                    && (forall x₁₈: int ::
                                                                          (x₁₈ == 0
                                                                             ==> (exists i₁₇: int ::
                                                                                    i₁₇ < N₂₇
                                                                                    && x₁₈ == 0
                                                                                    && sum₃₄[x₁₈] == a₃₂[i₁₇] + sum₃₀[0 := 1][0])))
                                                                    && (forall x₁₈: int ::
                                                                            x₁₈ == 0
                                                                            || sum₃₄[x₁₈] == sum₃₀[0 := 1][x₁₈])
                                                                    && (forall i₁₇: int ::
                                                                          (  0 <= i₁₇
                                                                            && i₁₇ < i₃₅
                                                                             ==> i₁₇ < N₂₇))
                                                                     ==> (i₃₅ < N₂₇
                                                                         ==> 0 <= i₃₅ + 1
                                                                          && i₃₅ + 1 <= N₂₇
                                                                          && (forall x₁₈: int ::
                                                                                (x₁₈ == 0
                                                                                   ==> (exists i₁₇: int ::
                                                                                          i₁₇ < N₂₇
                                                                                          && x₁₈ == 0
                                                                                          && sum₃₄[0 := sum₃₄[0] + a₃₂[i₃₅]][x₁₈] == a₃₂[i₁₇] + sum₃₀[0 := 1][0])))
                                                                          && (forall x₁₈: int ::
                                                                                  x₁₈ == 0
                                                                                  || sum₃₄[0 := sum₃₄[0] + a₃₂[i₃₅]][x₁₈] == sum₃₀[0 := 1][x₁₈])
                                                                          && (forall i₁₇: int ::
                                                                                (  0 <= i₁₇
                                                                                  && i₁₇ < i₃₅ + 1
                                                                                   ==> i₁₇ < N₂₇)))
                                                                      &&   i₃₅ < N₂₇
                                                                        ||   0 <= 0
                                                                          && 0 <= N₂₇
                                                                          && (forall x₂₂: int, i₂₁: int ::
                                                                                (  x₂₂ == i₂₁
                                                                                  && 0 <= i₂₁
                                                                                  && i₂₁ < 0
                                                                                   ==> (exists i₂₁: int ::
                                                                                          i₂₁ < N₂₇
                                                                                          && x₂₂ == i₂₁
                                                                                          && 0 <= i₂₁
                                                                                          && i₂₁ < 0
                                                                                          && a₃₂[x₂₂] == a₃₂[i₂₁] + sum₃₄[0])))
                                                                          && (forall x₂₂: int ::
                                                                                  (exists i₂₁: int ::
                                                                                          x₂₂ == i₂₁
                                                                                          && 0 <= i₂₁
                                                                                          && i₂₁ < 0)
                                                                                  || a₃₂[x₂₂] == a₃₂[x₂₂])
                                                                          && (forall i₂₁: int ::
                                                                                (  0 <= i₂₁
                                                                                  && i₂₁ < 0
                                                                                   ==> i₂₁ < N₂₇))
                                                                          && (forall a₃₆: [int]int, i₃₇: int ::
                                                                                (  0 <= i₃₇
                                                                                  && i₃₇ <= N₂₇
                                                                                  && (forall x₂₂: int, i₂₁: int ::
                                                                                        (  x₂₂ == i₂₁
                                                                                          && 0 <= i₂₁
                                                                                          && i₂₁ < i₃₇
                                                                                           ==> (exists i₂₁: int ::
                                                                                                  i₂₁ < N₂₇
                                                                                                  && x₂₂ == i₂₁
                                                                                                  && 0 <= i₂₁
                                                                                                  && i₂₁ < i₃₇
                                                                                                  && a₃₆[x₂₂] == a₃₂[i₂₁] + sum₃₄[0])))
                                                                                  && (forall x₂₂: int ::
                                                                                          (exists i₂₁: int ::
                                                                                                  x₂₂ == i₂₁
                                                                                                  && 0 <= i₂₁
                                                                                                  && i₂₁ < i₃₇)
                                                                                          || a₃₆[x₂₂] == a₃₂[x₂₂])
                                                                                  && (forall i₂₁: int ::
                                                                                        (  0 <= i₂₁
                                                                                          && i₂₁ < i₃₇
                                                                                           ==> i₂₁ < N₂₇))
                                                                                   ==> (i₃₇ < N₂₇
                                                                                       ==> 0 <= i₃₇ + 1
                                                                                        && i₃₇ + 1 <= N₂₇
                                                                                        && (forall x₂₂: int, i₂₁: int ::
                                                                                              (  x₂₂ == i₂₁
                                                                                                && 0 <= i₂₁
                                                                                                && i₂₁ < i₃₇ + 1
                                                                                                 ==> (exists i₂₁: int ::
                                                                                                        i₂₁ < N₂₇
                                                                                                        && x₂₂ == i₂₁
                                                                                                        && 0 <= i₂₁
                                                                                                        && i₂₁ < i₃₇ + 1
                                                                                                        && a₃₆[i₃₇ := a₃₆[i₃₇] + sum₃₄[0]][x₂₂] == a₃₂[i₂₁] + sum₃₄[0])))
                                                                                        && (forall x₂₂: int ::
                                                                                                (exists i₂₁: int ::
                                                                                                        x₂₂ == i₂₁
                                                                                                        && 0 <= i₂₁
                                                                                                        && i₂₁ < i₃₇ + 1)
                                                                                                || a₃₆[i₃₇ := a₃₆[i₃₇] + sum₃₄[0]][x₂₂] == a₃₂[x₂₂])
                                                                                        && (forall i₂₁: int ::
                                                                                              (  0 <= i₂₁
                                                                                                && i₂₁ < i₃₇ + 1
                                                                                                 ==> i₂₁ < N₂₇)))
                                                                                    &&   i₃₇ < N₂₇
                                                                                      ||   0 <= 0
                                                                                        && 0 <= N₂₇
                                                                                        && (forall i₂₅: int ::
                                                                                              (  0 <= i₂₅
                                                                                                && i₂₅ < 0
                                                                                                 ==> i₂₅ < N₂₇))
                                                                                        && (forall i₃₈: int ::
                                                                                              (  0 <= i₃₈
                                                                                                && i₃₈ <= N₂₇
                                                                                                && (forall i₂₅: int ::
                                                                                                      (  0 <= i₂₅
                                                                                                        && i₂₅ < i₃₈
                                                                                                         ==> i₂₅ < N₂₇))
                                                                                                 ==> (i₃₈ < N₂₇
                                                                                                   ==> a₃₆[i₃₈] == (N₂₇ + 1) * (N₂₇ + 1)
                                                                                                    && 0 <= i₃₈ + 1
                                                                                                    && i₃₈ + 1 <= N₂₇
                                                                                                    && (forall i₂₅: int ::
                                                                                                          (  0 <= i₂₅
                                                                                                            && i₂₅ < i₃₈ + 1
                                                                                                             ==> i₂₅ < N₂₇))))))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₃₁: int ::
        N₃₁ <= 0
        || (forall sum: [int]int, a: [int]int ::
              (N₃₁ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₃₁
                  && (forall x₆: int, i₅: int ::
                        (  x₆ == i₅
                          && 0 <= i₅
                          && i₅ < 0
                           ==> (exists i₅: int ::
                                  i₅ < N₃₁
                                  && x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0
                                  && a[x₆] == 2)))
                  && (forall x₆: int ::
                          (exists i₅: int ::
                                  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                          || a[x₆] == a[x₆])
                  && (forall i₅: int ::
                        (  0 <= i₅
                          && i₅ < 0
                           ==> i₅ < N₃₁))
                  && (forall a₃₂: [int]int, i₃₃: int ::
                        (  0 <= i₃₃
                          && i₃₃ <= N₃₁
                          && (forall x₆: int, i₅: int ::
                                (  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < i₃₃
                                   ==> (exists i₅: int ::
                                          i₅ < N₃₁
                                          && x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₃₃
                                          && a₃₂[x₆] == 2)))
                          && (forall x₆: int ::
                                  (exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₃₃)
                                  || a₃₂[x₆] == a[x₆])
                          && (forall i₅: int ::
                                (  0 <= i₅
                                  && i₅ < i₃₃
                                   ==> i₅ < N₃₁))
                           ==> (i₃₃ < N₃₁
                               ==> 0 <= i₃₃ + 1
                                && i₃₃ + 1 <= N₃₁
                                && (forall x₆: int, i₅: int ::
                                      (  x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₃₃ + 1
                                         ==> (exists i₅: int ::
                                                i₅ < N₃₁
                                                && x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₃₃ + 1
                                                && a₃₂[i₃₃ := 2][x₆] == 2)))
                                && (forall x₆: int ::
                                        (exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₃₃ + 1)
                                        || a₃₂[i₃₃ := 2][x₆] == a[x₆])
                                && (forall i₅: int ::
                                      (  0 <= i₅
                                        && i₅ < i₃₃ + 1
                                         ==> i₅ < N₃₁)))
                            &&   i₃₃ < N₃₁
                              ||   0 <= 0
                                && 0 <= N₃₁
                                && (forall x₁₀: int ::
                                      (x₁₀ == 0
                                         ==> (exists i₉: int ::
                                                i₉ < N₃₁
                                                && x₁₀ == 0
                                                && sum[0 := 0][x₁₀] == sum[0 := 0][0] + a₃₂[i₉])))
                                && (forall x₁₀: int ::
                                        x₁₀ == 0
                                        || sum[0 := 0][x₁₀] == sum[0 := 0][x₁₀])
                                && (forall i₉: int ::
                                      (  0 <= i₉
                                        && i₉ < 0
                                         ==> i₉ < N₃₁))
                                && (forall sum₃₄: [int]int, i₃₅: int ::
                                      (  0 <= i₃₅
                                        && i₃₅ <= N₃₁
                                        && (forall x₁₀: int ::
                                              (x₁₀ == 0
                                                 ==> (exists i₉: int ::
                                                        i₉ < N₃₁
                                                        && x₁₀ == 0
                                                        && sum₃₄[x₁₀] == sum[0 := 0][0] + a₃₂[i₉])))
                                        && (forall x₁₀: int ::
                                                x₁₀ == 0
                                                || sum₃₄[x₁₀] == sum[0 := 0][x₁₀])
                                        && (forall i₉: int ::
                                              (  0 <= i₉
                                                && i₉ < i₃₅
                                                 ==> i₉ < N₃₁))
                                         ==> (i₃₅ < N₃₁
                                             ==> 0 <= i₃₅ + 1
                                              && i₃₅ + 1 <= N₃₁
                                              && (forall x₁₀: int ::
                                                    (x₁₀ == 0
                                                       ==> (exists i₉: int ::
                                                              i₉ < N₃₁
                                                              && x₁₀ == 0
                                                              && sum₃₄[0 := sum₃₄[0] + a₃₂[i₃₅]][x₁₀] == sum[0 := 0][0] + a₃₂[i₉])))
                                              && (forall x₁₀: int ::
                                                      x₁₀ == 0
                                                      || sum₃₄[0 := sum₃₄[0] + a₃₂[i₃₅]][x₁₀] == sum[0 := 0][x₁₀])
                                              && (forall i₉: int ::
                                                    (  0 <= i₉
                                                      && i₉ < i₃₅ + 1
                                                       ==> i₉ < N₃₁)))
                                          &&   i₃₅ < N₃₁
                                            ||   0 <= 0
                                              && 0 <= N₃₁
                                              && (forall x₁₄: int, i₁₃: int ::
                                                    (  x₁₄ == i₁₃
                                                      && 0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> (exists i₁₃: int ::
                                                              i₁₃ < N₃₁
                                                              && x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < 0
                                                              && a₃₂[x₁₄] == 0)))
                                              && (forall x₁₄: int ::
                                                      (exists i₁₃: int ::
                                                              x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < 0)
                                                      || a₃₂[x₁₄] == a₃₂[x₁₄])
                                              && (forall i₁₃: int ::
                                                    (  0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> i₁₃ < N₃₁))
                                              && (forall a₃₆: [int]int, i₃₇: int ::
                                                    (  0 <= i₃₇
                                                      && i₃₇ <= N₃₁
                                                      && (forall x₁₄: int, i₁₃: int ::
                                                            (  x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < i₃₇
                                                               ==> (exists i₁₃: int ::
                                                                      i₁₃ < N₃₁
                                                                      && x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₃₇
                                                                      && a₃₆[x₁₄] == 0)))
                                                      && (forall x₁₄: int ::
                                                              (exists i₁₃: int ::
                                                                      x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₃₇)
                                                              || a₃₆[x₁₄] == a₃₂[x₁₄])
                                                      && (forall i₁₃: int ::
                                                            (  0 <= i₁₃
                                                              && i₁₃ < i₃₇
                                                               ==> i₁₃ < N₃₁))
                                                       ==> (i₃₇ < N₃₁
                                                           ==> 0 <= i₃₇ + 1
                                                            && i₃₇ + 1 <= N₃₁
                                                            && (forall x₁₄: int, i₁₃: int ::
                                                                  (  x₁₄ == i₁₃
                                                                    && 0 <= i₁₃
                                                                    && i₁₃ < i₃₇ + 1
                                                                     ==> (exists i₁₃: int ::
                                                                            i₁₃ < N₃₁
                                                                            && x₁₄ == i₁₃
                                                                            && 0 <= i₁₃
                                                                            && i₁₃ < i₃₇ + 1
                                                                            && a₃₆[i₃₇ := 0][x₁₄] == 0)))
                                                            && (forall x₁₄: int ::
                                                                    (exists i₁₃: int ::
                                                                            x₁₄ == i₁₃
                                                                            && 0 <= i₁₃
                                                                            && i₁₃ < i₃₇ + 1)
                                                                    || a₃₆[i₃₇ := 0][x₁₄] == a₃₂[x₁₄])
                                                            && (forall i₁₃: int ::
                                                                  (  0 <= i₁₃
                                                                    && i₁₃ < i₃₇ + 1
                                                                     ==> i₁₃ < N₃₁)))
                                                        &&   i₃₇ < N₃₁
                                                          ||   0 <= 0
                                                            && 0 <= N₃₁
                                                            && (forall x₁₈: int, i₁₇: int ::
                                                                  (  x₁₈ == i₁₇
                                                                    && 0 <= i₁₇
                                                                    && i₁₇ < 0
                                                                     ==> (exists i₁₇: int ::
                                                                            i₁₇ < N₃₁
                                                                            && x₁₈ == i₁₇
                                                                            && 0 <= i₁₇
                                                                            && i₁₇ < 0
                                                                            && a₃₆[x₁₈] == sum₃₄[0] + a₃₆[i₁₇])))
                                                            && (forall x₁₈: int ::
                                                                    (exists i₁₇: int ::
                                                                            x₁₈ == i₁₇
                                                                            && 0 <= i₁₇
                                                                            && i₁₇ < 0)
                                                                    || a₃₆[x₁₈] == a₃₆[x₁₈])
                                                            && (forall i₁₇: int ::
                                                                  (  0 <= i₁₇
                                                                    && i₁₇ < 0
                                                                     ==> i₁₇ < N₃₁))
                                                            && (forall a₃₈: [int]int, i₃₉: int ::
                                                                  (  0 <= i₃₉
                                                                    && i₃₉ <= N₃₁
                                                                    && (forall x₁₈: int, i₁₇: int ::
                                                                          (  x₁₈ == i₁₇
                                                                            && 0 <= i₁₇
                                                                            && i₁₇ < i₃₉
                                                                             ==> (exists i₁₇: int ::
                                                                                    i₁₇ < N₃₁
                                                                                    && x₁₈ == i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < i₃₉
                                                                                    && a₃₈[x₁₈] == sum₃₄[0] + a₃₆[i₁₇])))
                                                                    && (forall x₁₈: int ::
                                                                            (exists i₁₇: int ::
                                                                                    x₁₈ == i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < i₃₉)
                                                                            || a₃₈[x₁₈] == a₃₆[x₁₈])
                                                                    && (forall i₁₇: int ::
                                                                          (  0 <= i₁₇
                                                                            && i₁₇ < i₃₉
                                                                             ==> i₁₇ < N₃₁))
                                                                     ==> (i₃₉ < N₃₁
                                                                         ==> 0 <= i₃₉ + 1
                                                                          && i₃₉ + 1 <= N₃₁
                                                                          && (forall x₁₈: int, i₁₇: int ::
                                                                                (  x₁₈ == i₁₇
                                                                                  && 0 <= i₁₇
                                                                                  && i₁₇ < i₃₉ + 1
                                                                                   ==> (exists i₁₇: int ::
                                                                                          i₁₇ < N₃₁
                                                                                          && x₁₈ == i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₃₉ + 1
                                                                                          && a₃₈[i₃₉ := a₃₈[i₃₉] + sum₃₄[0]][x₁₈] == sum₃₄[0] + a₃₆[i₁₇])))
                                                                          && (forall x₁₈: int ::
                                                                                  (exists i₁₇: int ::
                                                                                          x₁₈ == i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₃₉ + 1)
                                                                                  || a₃₈[i₃₉ := a₃₈[i₃₉] + sum₃₄[0]][x₁₈] == a₃₆[x₁₈])
                                                                          && (forall i₁₇: int ::
                                                                                (  0 <= i₁₇
                                                                                  && i₁₇ < i₃₉ + 1
                                                                                   ==> i₁₇ < N₃₁)))
                                                                      &&   i₃₉ < N₃₁
                                                                        ||   0 <= 0
                                                                          && 0 <= N₃₁
                                                                          && (forall x₂₂: int ::
                                                                                (x₂₂ == 0
                                                                                   ==> (exists i₂₁: int ::
                                                                                          i₂₁ < N₃₁
                                                                                          && x₂₂ == 0
                                                                                          && sum₃₄[x₂₂] == sum₃₄[0] + a₃₈[i₂₁])))
                                                                          && (forall x₂₂: int ::
                                                                                  x₂₂ == 0
                                                                                  || sum₃₄[x₂₂] == sum₃₄[x₂₂])
                                                                          && (forall i₂₁: int ::
                                                                                (  0 <= i₂₁
                                                                                  && i₂₁ < 0
                                                                                   ==> i₂₁ < N₃₁))
                                                                          && (forall sum₄₀: [int]int, i₄₁: int ::
                                                                                (  0 <= i₄₁
                                                                                  && i₄₁ <= N₃₁
                                                                                  && (forall x₂₂: int ::
                                                                                        (x₂₂ == 0
                                                                                           ==> (exists i₂₁: int ::
                                                                                                  i₂₁ < N₃₁
                                                                                                  && x₂₂ == 0
                                                                                                  && sum₄₀[x₂₂] == sum₃₄[0] + a₃₈[i₂₁])))
                                                                                  && (forall x₂₂: int ::
                                                                                          x₂₂ == 0
                                                                                          || sum₄₀[x₂₂] == sum₃₄[x₂₂])
                                                                                  && (forall i₂₁: int ::
                                                                                        (  0 <= i₂₁
                                                                                          && i₂₁ < i₄₁
                                                                                           ==> i₂₁ < N₃₁))
                                                                                   ==> (i₄₁ < N₃₁
                                                                                       ==> 0 <= i₄₁ + 1
                                                                                        && i₄₁ + 1 <= N₃₁
                                                                                        && (forall x₂₂: int ::
                                                                                              (x₂₂ == 0
                                                                                                 ==> (exists i₂₁: int ::
                                                                                                        i₂₁ < N₃₁
                                                                                                        && x₂₂ == 0
                                                                                                        && sum₄₀[0 := sum₄₀[0] + a₃₈[i₄₁]][x₂₂] == sum₃₄[0] + a₃₈[i₂₁])))
                                                                                        && (forall x₂₂: int ::
                                                                                                x₂₂ == 0
                                                                                                || sum₄₀[0 := sum₄₀[0] + a₃₈[i₄₁]][x₂₂] == sum₃₄[x₂₂])
                                                                                        && (forall i₂₁: int ::
                                                                                              (  0 <= i₂₁
                                                                                                && i₂₁ < i₄₁ + 1
                                                                                                 ==> i₂₁ < N₃₁)))
                                                                                    &&   i₄₁ < N₃₁
                                                                                      ||   0 <= 0
                                                                                        && 0 <= N₃₁
                                                                                        && (forall x₂₆: int, i₂₅: int ::
                                                                                              (  x₂₆ == i₂₅
                                                                                                && 0 <= i₂₅
                                                                                                && i₂₅ < 0
                                                                                                 ==> (exists i₂₅: int ::
                                                                                                        i₂₅ < N₃₁
                                                                                                        && x₂₆ == i₂₅
                                                                                                        && 0 <= i₂₅
                                                                                                        && i₂₅ < 0
                                                                                                        && a₃₈[x₂₆] == a₃₈[i₂₅] + sum₄₀[0])))
                                                                                        && (forall x₂₆: int ::
                                                                                                (exists i₂₅: int ::
                                                                                                        x₂₆ == i₂₅
                                                                                                        && 0 <= i₂₅
                                                                                                        && i₂₅ < 0)
                                                                                                || a₃₈[x₂₆] == a₃₈[x₂₆])
                                                                                        && (forall i₂₅: int ::
                                                                                              (  0 <= i₂₅
                                                                                                && i₂₅ < 0
                                                                                                 ==> i₂₅ < N₃₁))
                                                                                        && (forall a₄₂: [int]int, i₄₃: int ::
                                                                                              (  0 <= i₄₃
                                                                                                && i₄₃ <= N₃₁
                                                                                                && (forall x₂₆: int, i₂₅: int ::
                                                                                                      (  x₂₆ == i₂₅
                                                                                                        && 0 <= i₂₅
                                                                                                        && i₂₅ < i₄₃
                                                                                                         ==> (exists i₂₅: int ::
                                                                                                                i₂₅ < N₃₁
                                                                                                                && x₂₆ == i₂₅
                                                                                                                && 0 <= i₂₅
                                                                                                                && i₂₅ < i₄₃
                                                                                                                && a₄₂[x₂₆] == a₃₈[i₂₅] + sum₄₀[0])))
                                                                                                && (forall x₂₆: int ::
                                                                                                        (exists i₂₅: int ::
                                                                                                                x₂₆ == i₂₅
                                                                                                                && 0 <= i₂₅
                                                                                                                && i₂₅ < i₄₃)
                                                                                                        || a₄₂[x₂₆] == a₃₈[x₂₆])
                                                                                                && (forall i₂₅: int ::
                                                                                                      (  0 <= i₂₅
                                                                                                        && i₂₅ < i₄₃
                                                                                                         ==> i₂₅ < N₃₁))
                                                                                                 ==> (i₄₃ < N₃₁
                                                                                                     ==> 0 <= i₄₃ + 1
                                                                                                      && i₄₃ + 1 <= N₃₁
                                                                                                      && (forall x₂₆: int, i₂₅: int ::
                                                                                                            (  x₂₆ == i₂₅
                                                                                                              && 0 <= i₂₅
                                                                                                              && i₂₅ < i₄₃ + 1
                                                                                                               ==> (exists i₂₅: int ::
                                                                                                                      i₂₅ < N₃₁
                                                                                                                      && x₂₆ == i₂₅
                                                                                                                      && 0 <= i₂₅
                                                                                                                      && i₂₅ < i₄₃ + 1
                                                                                                                      && a₄₂[i₄₃ := a₄₂[i₄₃] + sum₄₀[0]][x₂₆] == a₃₈[i₂₅] + sum₄₀[0])))
                                                                                                      && (forall x₂₆: int ::
                                                                                                              (exists i₂₅: int ::
                                                                                                                      x₂₆ == i₂₅
                                                                                                                      && 0 <= i₂₅
                                                                                                                      && i₂₅ < i₄₃ + 1)
                                                                                                              || a₄₂[i₄₃ := a₄₂[i₄₃] + sum₄₀[0]][x₂₆] == a₃₈[x₂₆])
                                                                                                      && (forall i₂₅: int ::
                                                                                                            (  0 <= i₂₅
                                                                                                              && i₂₅ < i₄₃ + 1
                                                                                                               ==> i₂₅ < N₃₁)))
                                                                                                  &&   i₄₃ < N₃₁
                                                                                                    ||   0 <= 0
                                                                                                      && 0 <= N₃₁
                                                                                                      && (forall i₂₉: int ::
                                                                                                            (  0 <= i₂₉
                                                                                                              && i₂₉ < 0
                                                                                                               ==> i₂₉ < N₃₁))
                                                                                                      && (forall i₄₄: int ::
                                                                                                            (  0 <= i₄₄
                                                                                                              && i₄₄ <= N₃₁
                                                                                                              && (forall i₂₉: int ::
                                                                                                                    (  0 <= i₂₉
                                                                                                                      && i₂₉ < i₄₄
                                                                                                                       ==> i₂₉ < N₃₁))
                                                                                                               ==> (i₄₄ < N₃₁
                                                                                                                 ==> a₄₂[i₄₄] == N₃₁ * (N₃₁ + 2)
                                                                                                                  && 0 <= i₄₄ + 1
                                                                                                                  && i₄₄ + 1 <= N₃₁
                                                                                                                  && (forall i₂₉: int ::
                                                                                                                        (  0 <= i₂₉
                                                                                                                          && i₂₉ < i₄₄ + 1
                                                                                                                           ==> i₂₉ < N₃₁))))))))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

goal (forall N₂₅: int ::
        N₂₅ <= 0
        || (forall sum: [int]int, a: [int]int ::
              (N₂₅ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₂₅
                  && (forall x₆: int, i₅: int ::
                        (  x₆ == i₅
                          && 0 <= i₅
                          && i₅ < 0
                           ==> (exists i₅: int ::
                                  i₅ < N₂₅
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
                           ==> i₅ < N₂₅))
                  && (forall a₂₆: [int]int, i₂₇: int ::
                        (  0 <= i₂₇
                          && i₂₇ <= N₂₅
                          && (forall x₆: int, i₅: int ::
                                (  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < i₂₇
                                   ==> (exists i₅: int ::
                                          i₅ < N₂₅
                                          && x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₇
                                          && a₂₆[x₆] == 1)))
                          && (forall x₆: int ::
                                  (exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₇)
                                  || a₂₆[x₆] == a[x₆])
                          && (forall i₅: int ::
                                (  0 <= i₅
                                  && i₅ < i₂₇
                                   ==> i₅ < N₂₅))
                           ==> (i₂₇ < N₂₅
                               ==> 0 <= i₂₇ + 1
                                && i₂₇ + 1 <= N₂₅
                                && (forall x₆: int, i₅: int ::
                                      (  x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₂₇ + 1
                                         ==> (exists i₅: int ::
                                                i₅ < N₂₅
                                                && x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₇ + 1
                                                && a₂₆[i₂₇ := 1][x₆] == 1)))
                                && (forall x₆: int ::
                                        (exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₇ + 1)
                                        || a₂₆[i₂₇ := 1][x₆] == a[x₆])
                                && (forall i₅: int ::
                                      (  0 <= i₅
                                        && i₅ < i₂₇ + 1
                                         ==> i₅ < N₂₅)))
                            &&   i₂₇ < N₂₅
                              ||   0 <= 0
                                && 0 <= N₂₅
                                && (forall x₁₀: int ::
                                      (x₁₀ == 0
                                         ==> (exists i₉: int ::
                                                i₉ < N₂₅
                                                && x₁₀ == 0
                                                && sum[0 := 0][x₁₀] == sum[0 := 0][0] + a₂₆[i₉])))
                                && (forall x₁₀: int ::
                                        x₁₀ == 0
                                        || sum[0 := 0][x₁₀] == sum[0 := 0][x₁₀])
                                && (forall i₉: int ::
                                      (  0 <= i₉
                                        && i₉ < 0
                                         ==> i₉ < N₂₅))
                                && (forall sum₂₈: [int]int, i₂₉: int ::
                                      (  0 <= i₂₉
                                        && i₂₉ <= N₂₅
                                        && (forall x₁₀: int ::
                                              (x₁₀ == 0
                                                 ==> (exists i₉: int ::
                                                        i₉ < N₂₅
                                                        && x₁₀ == 0
                                                        && sum₂₈[x₁₀] == sum[0 := 0][0] + a₂₆[i₉])))
                                        && (forall x₁₀: int ::
                                                x₁₀ == 0
                                                || sum₂₈[x₁₀] == sum[0 := 0][x₁₀])
                                        && (forall i₉: int ::
                                              (  0 <= i₉
                                                && i₉ < i₂₉
                                                 ==> i₉ < N₂₅))
                                         ==> (i₂₉ < N₂₅
                                             ==> 0 <= i₂₉ + 1
                                              && i₂₉ + 1 <= N₂₅
                                              && (forall x₁₀: int ::
                                                    (x₁₀ == 0
                                                       ==> (exists i₉: int ::
                                                              i₉ < N₂₅
                                                              && x₁₀ == 0
                                                              && sum₂₈[0 := sum₂₈[0] + a₂₆[i₂₉]][x₁₀] == sum[0 := 0][0] + a₂₆[i₉])))
                                              && (forall x₁₀: int ::
                                                      x₁₀ == 0
                                                      || sum₂₈[0 := sum₂₈[0] + a₂₆[i₂₉]][x₁₀] == sum[0 := 0][x₁₀])
                                              && (forall i₉: int ::
                                                    (  0 <= i₉
                                                      && i₉ < i₂₉ + 1
                                                       ==> i₉ < N₂₅)))
                                          &&   i₂₉ < N₂₅
                                            ||   0 <= 0
                                              && 0 <= N₂₅
                                              && (forall x₁₄: int, i₁₃: int ::
                                                    (  x₁₄ == i₁₃
                                                      && 0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> (exists i₁₃: int ::
                                                              i₁₃ < N₂₅
                                                              && x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < 0
                                                              && a₂₆[x₁₄] == -1)))
                                              && (forall x₁₄: int ::
                                                      (exists i₁₃: int ::
                                                              x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < 0)
                                                      || a₂₆[x₁₄] == a₂₆[x₁₄])
                                              && (forall i₁₃: int ::
                                                    (  0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> i₁₃ < N₂₅))
                                              && (forall a₃₀: [int]int, i₃₁: int ::
                                                    (  0 <= i₃₁
                                                      && i₃₁ <= N₂₅
                                                      && (forall x₁₄: int, i₁₃: int ::
                                                            (  x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < i₃₁
                                                               ==> (exists i₁₃: int ::
                                                                      i₁₃ < N₂₅
                                                                      && x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₃₁
                                                                      && a₃₀[x₁₄] == -1)))
                                                      && (forall x₁₄: int ::
                                                              (exists i₁₃: int ::
                                                                      x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₃₁)
                                                              || a₃₀[x₁₄] == a₂₆[x₁₄])
                                                      && (forall i₁₃: int ::
                                                            (  0 <= i₁₃
                                                              && i₁₃ < i₃₁
                                                               ==> i₁₃ < N₂₅))
                                                       ==> (i₃₁ < N₂₅
                                                           ==> 0 <= i₃₁ + 1
                                                            && i₃₁ + 1 <= N₂₅
                                                            && (forall x₁₄: int, i₁₃: int ::
                                                                  (  x₁₄ == i₁₃
                                                                    && 0 <= i₁₃
                                                                    && i₁₃ < i₃₁ + 1
                                                                     ==> (exists i₁₃: int ::
                                                                            i₁₃ < N₂₅
                                                                            && x₁₄ == i₁₃
                                                                            && 0 <= i₁₃
                                                                            && i₁₃ < i₃₁ + 1
                                                                            && a₃₀[i₃₁ := -1][x₁₄] == -1)))
                                                            && (forall x₁₄: int ::
                                                                    (exists i₁₃: int ::
                                                                            x₁₄ == i₁₃
                                                                            && 0 <= i₁₃
                                                                            && i₁₃ < i₃₁ + 1)
                                                                    || a₃₀[i₃₁ := -1][x₁₄] == a₂₆[x₁₄])
                                                            && (forall i₁₃: int ::
                                                                  (  0 <= i₁₃
                                                                    && i₁₃ < i₃₁ + 1
                                                                     ==> i₁₃ < N₂₅)))
                                                        &&   i₃₁ < N₂₅
                                                          ||   0 <= 0
                                                            && 0 <= N₂₅
                                                            && (forall x₁₈: int, i₁₇: int ::
                                                                  (  x₁₈ == i₁₇
                                                                    && 0 <= i₁₇
                                                                    && i₁₇ < 0
                                                                     ==> (exists i₁₇: int ::
                                                                            i₁₇ < N₂₅
                                                                            && x₁₈ == i₁₇
                                                                            && 0 <= i₁₇
                                                                            && i₁₇ < 0
                                                                            && a₃₀[x₁₈] == sum₂₈[0] + a₃₀[i₁₇])))
                                                            && (forall x₁₈: int ::
                                                                    (exists i₁₇: int ::
                                                                            x₁₈ == i₁₇
                                                                            && 0 <= i₁₇
                                                                            && i₁₇ < 0)
                                                                    || a₃₀[x₁₈] == a₃₀[x₁₈])
                                                            && (forall i₁₇: int ::
                                                                  (  0 <= i₁₇
                                                                    && i₁₇ < 0
                                                                     ==> i₁₇ < N₂₅))
                                                            && (forall a₃₂: [int]int, i₃₃: int ::
                                                                  (  0 <= i₃₃
                                                                    && i₃₃ <= N₂₅
                                                                    && (forall x₁₈: int, i₁₇: int ::
                                                                          (  x₁₈ == i₁₇
                                                                            && 0 <= i₁₇
                                                                            && i₁₇ < i₃₃
                                                                             ==> (exists i₁₇: int ::
                                                                                    i₁₇ < N₂₅
                                                                                    && x₁₈ == i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < i₃₃
                                                                                    && a₃₂[x₁₈] == sum₂₈[0] + a₃₀[i₁₇])))
                                                                    && (forall x₁₈: int ::
                                                                            (exists i₁₇: int ::
                                                                                    x₁₈ == i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < i₃₃)
                                                                            || a₃₂[x₁₈] == a₃₀[x₁₈])
                                                                    && (forall i₁₇: int ::
                                                                          (  0 <= i₁₇
                                                                            && i₁₇ < i₃₃
                                                                             ==> i₁₇ < N₂₅))
                                                                     ==> (i₃₃ < N₂₅
                                                                         ==> 0 <= i₃₃ + 1
                                                                          && i₃₃ + 1 <= N₂₅
                                                                          && (forall x₁₈: int, i₁₇: int ::
                                                                                (  x₁₈ == i₁₇
                                                                                  && 0 <= i₁₇
                                                                                  && i₁₇ < i₃₃ + 1
                                                                                   ==> (exists i₁₇: int ::
                                                                                          i₁₇ < N₂₅
                                                                                          && x₁₈ == i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₃₃ + 1
                                                                                          && a₃₂[i₃₃ := a₃₂[i₃₃] + sum₂₈[0]][x₁₈] == sum₂₈[0] + a₃₀[i₁₇])))
                                                                          && (forall x₁₈: int ::
                                                                                  (exists i₁₇: int ::
                                                                                          x₁₈ == i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₃₃ + 1)
                                                                                  || a₃₂[i₃₃ := a₃₂[i₃₃] + sum₂₈[0]][x₁₈] == a₃₀[x₁₈])
                                                                          && (forall i₁₇: int ::
                                                                                (  0 <= i₁₇
                                                                                  && i₁₇ < i₃₃ + 1
                                                                                   ==> i₁₇ < N₂₅)))
                                                                      &&   i₃₃ < N₂₅
                                                                        ||   0 <= 0
                                                                          && 0 <= N₂₅
                                                                          && (forall x₂₂: int ::
                                                                                (x₂₂ == 0
                                                                                   ==> (exists i₂₁: int ::
                                                                                          i₂₁ < N₂₅
                                                                                          && x₂₂ == 0
                                                                                          && sum₂₈[x₂₂] == sum₂₈[0] + a₃₂[i₂₁])))
                                                                          && (forall x₂₂: int ::
                                                                                  x₂₂ == 0
                                                                                  || sum₂₈[x₂₂] == sum₂₈[x₂₂])
                                                                          && (forall i₂₁: int ::
                                                                                (  0 <= i₂₁
                                                                                  && i₂₁ < 0
                                                                                   ==> i₂₁ < N₂₅))
                                                                          && (forall sum₃₄: [int]int, i₃₅: int ::
                                                                                (  0 <= i₃₅
                                                                                  && i₃₅ <= N₂₅
                                                                                  && (forall x₂₂: int ::
                                                                                        (x₂₂ == 0
                                                                                           ==> (exists i₂₁: int ::
                                                                                                  i₂₁ < N₂₅
                                                                                                  && x₂₂ == 0
                                                                                                  && sum₃₄[x₂₂] == sum₂₈[0] + a₃₂[i₂₁])))
                                                                                  && (forall x₂₂: int ::
                                                                                          x₂₂ == 0
                                                                                          || sum₃₄[x₂₂] == sum₂₈[x₂₂])
                                                                                  && (forall i₂₁: int ::
                                                                                        (  0 <= i₂₁
                                                                                          && i₂₁ < i₃₅
                                                                                           ==> i₂₁ < N₂₅))
                                                                                   ==> (i₃₅ < N₂₅
                                                                                       ==> 0 <= i₃₅ + 1
                                                                                        && i₃₅ + 1 <= N₂₅
                                                                                        && (forall x₂₂: int ::
                                                                                              (x₂₂ == 0
                                                                                                 ==> (exists i₂₁: int ::
                                                                                                        i₂₁ < N₂₅
                                                                                                        && x₂₂ == 0
                                                                                                        && sum₃₄[0 := sum₃₄[0] + a₃₂[i₃₅]][x₂₂] == sum₂₈[0] + a₃₂[i₂₁])))
                                                                                        && (forall x₂₂: int ::
                                                                                                x₂₂ == 0
                                                                                                || sum₃₄[0 := sum₃₄[0] + a₃₂[i₃₅]][x₂₂] == sum₂₈[x₂₂])
                                                                                        && (forall i₂₁: int ::
                                                                                              (  0 <= i₂₁
                                                                                                && i₂₁ < i₃₅ + 1
                                                                                                 ==> i₂₁ < N₂₅)))
                                                                                    &&   i₃₅ < N₂₅
                                                                                      || sum₃₄[0] == N₂₅ * (N₂₅ + 1))))))))))))));


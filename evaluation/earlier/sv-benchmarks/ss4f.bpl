data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

goal (forall N₂₁: int ::
        N₂₁ <= 0
        || (forall sum: [int]int, a: [int]int ::
              (N₂₁ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₂₁
                  && (forall x₆: int, i₅: int ::
                        (  x₆ == i₅
                          && 0 <= i₅
                          && i₅ < 0
                           ==> (exists i₅: int ::
                                  i₅ < N₂₁
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
                           ==> i₅ < N₂₁))
                  && (forall a₂₂: [int]int, i₂₃: int ::
                        (  0 <= i₂₃
                          && i₂₃ <= N₂₁
                          && (forall x₆: int, i₅: int ::
                                (  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < i₂₃
                                   ==> (exists i₅: int ::
                                          i₅ < N₂₁
                                          && x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₃
                                          && a₂₂[x₆] == 1)))
                          && (forall x₆: int ::
                                  (exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₂₃)
                                  || a₂₂[x₆] == a[x₆])
                          && (forall i₅: int ::
                                (  0 <= i₅
                                  && i₅ < i₂₃
                                   ==> i₅ < N₂₁))
                           ==> (i₂₃ < N₂₁
                               ==> 0 <= i₂₃ + 1
                                && i₂₃ + 1 <= N₂₁
                                && (forall x₆: int, i₅: int ::
                                      (  x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₂₃ + 1
                                         ==> (exists i₅: int ::
                                                i₅ < N₂₁
                                                && x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₃ + 1
                                                && a₂₂[i₂₃ := 1][x₆] == 1)))
                                && (forall x₆: int ::
                                        (exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₃ + 1)
                                        || a₂₂[i₂₃ := 1][x₆] == a[x₆])
                                && (forall i₅: int ::
                                      (  0 <= i₅
                                        && i₅ < i₂₃ + 1
                                         ==> i₅ < N₂₁)))
                            &&   i₂₃ < N₂₁
                              ||   0 <= 0
                                && 0 <= N₂₁
                                && (forall x₁₀: int ::
                                      (x₁₀ == 0
                                         ==> (exists i₉: int ::
                                                i₉ < N₂₁
                                                && x₁₀ == 0
                                                && sum[0 := 0][x₁₀] == sum[0 := 0][0] + a₂₂[i₉])))
                                && (forall x₁₀: int ::
                                        x₁₀ == 0
                                        || sum[0 := 0][x₁₀] == sum[0 := 0][x₁₀])
                                && (forall i₉: int ::
                                      (  0 <= i₉
                                        && i₉ < 0
                                         ==> i₉ < N₂₁))
                                && (forall sum₂₄: [int]int, i₂₅: int ::
                                      (  0 <= i₂₅
                                        && i₂₅ <= N₂₁
                                        && (forall x₁₀: int ::
                                              (x₁₀ == 0
                                                 ==> (exists i₉: int ::
                                                        i₉ < N₂₁
                                                        && x₁₀ == 0
                                                        && sum₂₄[x₁₀] == sum[0 := 0][0] + a₂₂[i₉])))
                                        && (forall x₁₀: int ::
                                                x₁₀ == 0
                                                || sum₂₄[x₁₀] == sum[0 := 0][x₁₀])
                                        && (forall i₉: int ::
                                              (  0 <= i₉
                                                && i₉ < i₂₅
                                                 ==> i₉ < N₂₁))
                                         ==> (i₂₅ < N₂₁
                                             ==> 0 <= i₂₅ + 1
                                              && i₂₅ + 1 <= N₂₁
                                              && (forall x₁₀: int ::
                                                    (x₁₀ == 0
                                                       ==> (exists i₉: int ::
                                                              i₉ < N₂₁
                                                              && x₁₀ == 0
                                                              && sum₂₄[0 := sum₂₄[0] + a₂₂[i₂₅]][x₁₀] == sum[0 := 0][0] + a₂₂[i₉])))
                                              && (forall x₁₀: int ::
                                                      x₁₀ == 0
                                                      || sum₂₄[0 := sum₂₄[0] + a₂₂[i₂₅]][x₁₀] == sum[0 := 0][x₁₀])
                                              && (forall i₉: int ::
                                                    (  0 <= i₉
                                                      && i₉ < i₂₅ + 1
                                                       ==> i₉ < N₂₁)))
                                          &&   i₂₅ < N₂₁
                                            ||   0 <= 0
                                              && 0 <= N₂₁
                                              && (forall x₁₄: int, i₁₃: int ::
                                                    (  x₁₄ == i₁₃
                                                      && 0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> (exists i₁₃: int ::
                                                              i₁₃ < N₂₁
                                                              && x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < 0
                                                              && a₂₂[x₁₄] == sum₂₄[0] + a₂₂[i₁₃])))
                                              && (forall x₁₄: int ::
                                                      (exists i₁₃: int ::
                                                              x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < 0)
                                                      || a₂₂[x₁₄] == a₂₂[x₁₄])
                                              && (forall i₁₃: int ::
                                                    (  0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> i₁₃ < N₂₁))
                                              && (forall a₂₆: [int]int, i₂₇: int ::
                                                    (  0 <= i₂₇
                                                      && i₂₇ <= N₂₁
                                                      && (forall x₁₄: int, i₁₃: int ::
                                                            (  x₁₄ == i₁₃
                                                              && 0 <= i₁₃
                                                              && i₁₃ < i₂₇
                                                               ==> (exists i₁₃: int ::
                                                                      i₁₃ < N₂₁
                                                                      && x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₂₇
                                                                      && a₂₆[x₁₄] == sum₂₄[0] + a₂₂[i₁₃])))
                                                      && (forall x₁₄: int ::
                                                              (exists i₁₃: int ::
                                                                      x₁₄ == i₁₃
                                                                      && 0 <= i₁₃
                                                                      && i₁₃ < i₂₇)
                                                              || a₂₆[x₁₄] == a₂₂[x₁₄])
                                                      && (forall i₁₃: int ::
                                                            (  0 <= i₁₃
                                                              && i₁₃ < i₂₇
                                                               ==> i₁₃ < N₂₁))
                                                       ==> (i₂₇ < N₂₁
                                                           ==> 0 <= i₂₇ + 1
                                                            && i₂₇ + 1 <= N₂₁
                                                            && (forall x₁₄: int, i₁₃: int ::
                                                                  (  x₁₄ == i₁₃
                                                                    && 0 <= i₁₃
                                                                    && i₁₃ < i₂₇ + 1
                                                                     ==> (exists i₁₃: int ::
                                                                            i₁₃ < N₂₁
                                                                            && x₁₄ == i₁₃
                                                                            && 0 <= i₁₃
                                                                            && i₁₃ < i₂₇ + 1
                                                                            && a₂₆[i₂₇ := a₂₆[i₂₇] + sum₂₄[0]][x₁₄] == sum₂₄[0] + a₂₂[i₁₃])))
                                                            && (forall x₁₄: int ::
                                                                    (exists i₁₃: int ::
                                                                            x₁₄ == i₁₃
                                                                            && 0 <= i₁₃
                                                                            && i₁₃ < i₂₇ + 1)
                                                                    || a₂₆[i₂₇ := a₂₆[i₂₇] + sum₂₄[0]][x₁₄] == a₂₂[x₁₄])
                                                            && (forall i₁₃: int ::
                                                                  (  0 <= i₁₃
                                                                    && i₁₃ < i₂₇ + 1
                                                                     ==> i₁₃ < N₂₁)))
                                                        &&   i₂₇ < N₂₁
                                                          ||   0 <= 0
                                                            && 0 <= N₂₁
                                                            && (forall x₁₈: int ::
                                                                  (x₁₈ == 0
                                                                     ==> (exists i₁₇: int ::
                                                                            i₁₇ < N₂₁
                                                                            && x₁₈ == 0
                                                                            && sum₂₄[0 := N₂₁][x₁₈] == a₂₆[i₁₇] + sum₂₄[0 := N₂₁][0])))
                                                            && (forall x₁₈: int ::
                                                                    x₁₈ == 0
                                                                    || sum₂₄[0 := N₂₁][x₁₈] == sum₂₄[0 := N₂₁][x₁₈])
                                                            && (forall i₁₇: int ::
                                                                  (  0 <= i₁₇
                                                                    && i₁₇ < 0
                                                                     ==> i₁₇ < N₂₁))
                                                            && (forall sum₂₈: [int]int, i₂₉: int ::
                                                                  (  0 <= i₂₉
                                                                    && i₂₉ <= N₂₁
                                                                    && (forall x₁₈: int ::
                                                                          (x₁₈ == 0
                                                                             ==> (exists i₁₇: int ::
                                                                                    i₁₇ < N₂₁
                                                                                    && x₁₈ == 0
                                                                                    && sum₂₈[x₁₈] == a₂₆[i₁₇] + sum₂₄[0 := N₂₁][0])))
                                                                    && (forall x₁₈: int ::
                                                                            x₁₈ == 0
                                                                            || sum₂₈[x₁₈] == sum₂₄[0 := N₂₁][x₁₈])
                                                                    && (forall i₁₇: int ::
                                                                          (  0 <= i₁₇
                                                                            && i₁₇ < i₂₉
                                                                             ==> i₁₇ < N₂₁))
                                                                     ==> (i₂₉ < N₂₁
                                                                         ==> 0 <= i₂₉ + 1
                                                                          && i₂₉ + 1 <= N₂₁
                                                                          && (forall x₁₈: int ::
                                                                                (x₁₈ == 0
                                                                                   ==> (exists i₁₇: int ::
                                                                                          i₁₇ < N₂₁
                                                                                          && x₁₈ == 0
                                                                                          && sum₂₈[0 := sum₂₈[0] + a₂₆[i₂₉]][x₁₈] == a₂₆[i₁₇] + sum₂₄[0 := N₂₁][0])))
                                                                          && (forall x₁₈: int ::
                                                                                  x₁₈ == 0
                                                                                  || sum₂₈[0 := sum₂₈[0] + a₂₆[i₂₉]][x₁₈] == sum₂₄[0 := N₂₁][x₁₈])
                                                                          && (forall i₁₇: int ::
                                                                                (  0 <= i₁₇
                                                                                  && i₁₇ < i₂₉ + 1
                                                                                   ==> i₁₇ < N₂₁)))
                                                                      &&   i₂₉ < N₂₁
                                                                        || sum₂₈[0] == N₂₁ * (N₂₁ + 1))))))))))));


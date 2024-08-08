data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

goal (forall N₃₁: int ::
        N₃₁ <= 0
        || (forall sum: [int]int, a: [int]int, b: [int]int, c: [int]int ::
              (N₃₁ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₃₁
                  && (forall x₈: int, i₇: int ::
                        (  x₈ == i₇
                          && 0 <= i₇
                          && i₇ < 0
                           ==> (exists i₇: int ::
                                  i₇ < N₃₁
                                  && x₈ == i₇
                                  && 0 <= i₇
                                  && i₇ < 0
                                  && a[x₈] == 1)))
                  && (forall x₈: int ::
                          (exists i₇: int ::
                                  x₈ == i₇
                                  && 0 <= i₇
                                  && i₇ < 0)
                          || a[x₈] == a[x₈])
                  && (forall i₇: int ::
                        (  0 <= i₇
                          && i₇ < 0
                           ==> i₇ < N₃₁))
                  && (forall a₃₂: [int]int, i₃₃: int ::
                        (  0 <= i₃₃
                          && i₃₃ <= N₃₁
                          && (forall x₈: int, i₇: int ::
                                (  x₈ == i₇
                                  && 0 <= i₇
                                  && i₇ < i₃₃
                                   ==> (exists i₇: int ::
                                          i₇ < N₃₁
                                          && x₈ == i₇
                                          && 0 <= i₇
                                          && i₇ < i₃₃
                                          && a₃₂[x₈] == 1)))
                          && (forall x₈: int ::
                                  (exists i₇: int ::
                                          x₈ == i₇
                                          && 0 <= i₇
                                          && i₇ < i₃₃)
                                  || a₃₂[x₈] == a[x₈])
                          && (forall i₇: int ::
                                (  0 <= i₇
                                  && i₇ < i₃₃
                                   ==> i₇ < N₃₁))
                           ==> (i₃₃ < N₃₁
                               ==> 0 <= i₃₃ + 1
                                && i₃₃ + 1 <= N₃₁
                                && (forall x₈: int, i₇: int ::
                                      (  x₈ == i₇
                                        && 0 <= i₇
                                        && i₇ < i₃₃ + 1
                                         ==> (exists i₇: int ::
                                                i₇ < N₃₁
                                                && x₈ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₃₃ + 1
                                                && a₃₂[i₃₃ := 1][x₈] == 1)))
                                && (forall x₈: int ::
                                        (exists i₇: int ::
                                                x₈ == i₇
                                                && 0 <= i₇
                                                && i₇ < i₃₃ + 1)
                                        || a₃₂[i₃₃ := 1][x₈] == a[x₈])
                                && (forall i₇: int ::
                                      (  0 <= i₇
                                        && i₇ < i₃₃ + 1
                                         ==> i₇ < N₃₁)))
                            &&   i₃₃ < N₃₁
                              ||   0 <= 0
                                && 0 <= N₃₁
                                && (forall x₁₂: int, i₁₁: int ::
                                      (  x₁₂ == i₁₁
                                        && 0 <= i₁₁
                                        && i₁₁ < 0
                                         ==> (exists i₁₁: int ::
                                                i₁₁ < N₃₁
                                                && x₁₂ == i₁₁
                                                && 0 <= i₁₁
                                                && i₁₁ < 0
                                                && b[x₁₂] == 1)))
                                && (forall x₁₂: int ::
                                        (exists i₁₁: int ::
                                                x₁₂ == i₁₁
                                                && 0 <= i₁₁
                                                && i₁₁ < 0)
                                        || b[x₁₂] == b[x₁₂])
                                && (forall i₁₁: int ::
                                      (  0 <= i₁₁
                                        && i₁₁ < 0
                                         ==> i₁₁ < N₃₁))
                                && (forall b₃₄: [int]int, i₃₅: int ::
                                      (  0 <= i₃₅
                                        && i₃₅ <= N₃₁
                                        && (forall x₁₂: int, i₁₁: int ::
                                              (  x₁₂ == i₁₁
                                                && 0 <= i₁₁
                                                && i₁₁ < i₃₅
                                                 ==> (exists i₁₁: int ::
                                                        i₁₁ < N₃₁
                                                        && x₁₂ == i₁₁
                                                        && 0 <= i₁₁
                                                        && i₁₁ < i₃₅
                                                        && b₃₄[x₁₂] == 1)))
                                        && (forall x₁₂: int ::
                                                (exists i₁₁: int ::
                                                        x₁₂ == i₁₁
                                                        && 0 <= i₁₁
                                                        && i₁₁ < i₃₅)
                                                || b₃₄[x₁₂] == b[x₁₂])
                                        && (forall i₁₁: int ::
                                              (  0 <= i₁₁
                                                && i₁₁ < i₃₅
                                                 ==> i₁₁ < N₃₁))
                                         ==> (i₃₅ < N₃₁
                                             ==> 0 <= i₃₅ + 1
                                              && i₃₅ + 1 <= N₃₁
                                              && (forall x₁₂: int, i₁₁: int ::
                                                    (  x₁₂ == i₁₁
                                                      && 0 <= i₁₁
                                                      && i₁₁ < i₃₅ + 1
                                                       ==> (exists i₁₁: int ::
                                                              i₁₁ < N₃₁
                                                              && x₁₂ == i₁₁
                                                              && 0 <= i₁₁
                                                              && i₁₁ < i₃₅ + 1
                                                              && b₃₄[i₃₅ := 1][x₁₂] == 1)))
                                              && (forall x₁₂: int ::
                                                      (exists i₁₁: int ::
                                                              x₁₂ == i₁₁
                                                              && 0 <= i₁₁
                                                              && i₁₁ < i₃₅ + 1)
                                                      || b₃₄[i₃₅ := 1][x₁₂] == b[x₁₂])
                                              && (forall i₁₁: int ::
                                                    (  0 <= i₁₁
                                                      && i₁₁ < i₃₅ + 1
                                                       ==> i₁₁ < N₃₁)))
                                          &&   i₃₅ < N₃₁
                                            ||   0 <= 0
                                              && 0 <= N₃₁
                                              && (forall x₁₆: int, i₁₅: int ::
                                                    (  x₁₆ == i₁₅
                                                      && 0 <= i₁₅
                                                      && i₁₅ < 0
                                                       ==> (exists i₁₅: int ::
                                                              i₁₅ < N₃₁
                                                              && x₁₆ == i₁₅
                                                              && 0 <= i₁₅
                                                              && i₁₅ < 0
                                                              && c[x₁₆] == 1)))
                                              && (forall x₁₆: int ::
                                                      (exists i₁₅: int ::
                                                              x₁₆ == i₁₅
                                                              && 0 <= i₁₅
                                                              && i₁₅ < 0)
                                                      || c[x₁₆] == c[x₁₆])
                                              && (forall i₁₅: int ::
                                                    (  0 <= i₁₅
                                                      && i₁₅ < 0
                                                       ==> i₁₅ < N₃₁))
                                              && (forall c₃₆: [int]int, i₃₇: int ::
                                                    (  0 <= i₃₇
                                                      && i₃₇ <= N₃₁
                                                      && (forall x₁₆: int, i₁₅: int ::
                                                            (  x₁₆ == i₁₅
                                                              && 0 <= i₁₅
                                                              && i₁₅ < i₃₇
                                                               ==> (exists i₁₅: int ::
                                                                      i₁₅ < N₃₁
                                                                      && x₁₆ == i₁₅
                                                                      && 0 <= i₁₅
                                                                      && i₁₅ < i₃₇
                                                                      && c₃₆[x₁₆] == 1)))
                                                      && (forall x₁₆: int ::
                                                              (exists i₁₅: int ::
                                                                      x₁₆ == i₁₅
                                                                      && 0 <= i₁₅
                                                                      && i₁₅ < i₃₇)
                                                              || c₃₆[x₁₆] == c[x₁₆])
                                                      && (forall i₁₅: int ::
                                                            (  0 <= i₁₅
                                                              && i₁₅ < i₃₇
                                                               ==> i₁₅ < N₃₁))
                                                       ==> (i₃₇ < N₃₁
                                                           ==> 0 <= i₃₇ + 1
                                                            && i₃₇ + 1 <= N₃₁
                                                            && (forall x₁₆: int, i₁₅: int ::
                                                                  (  x₁₆ == i₁₅
                                                                    && 0 <= i₁₅
                                                                    && i₁₅ < i₃₇ + 1
                                                                     ==> (exists i₁₅: int ::
                                                                            i₁₅ < N₃₁
                                                                            && x₁₆ == i₁₅
                                                                            && 0 <= i₁₅
                                                                            && i₁₅ < i₃₇ + 1
                                                                            && c₃₆[i₃₇ := 1][x₁₆] == 1)))
                                                            && (forall x₁₆: int ::
                                                                    (exists i₁₅: int ::
                                                                            x₁₆ == i₁₅
                                                                            && 0 <= i₁₅
                                                                            && i₁₅ < i₃₇ + 1)
                                                                    || c₃₆[i₃₇ := 1][x₁₆] == c[x₁₆])
                                                            && (forall i₁₅: int ::
                                                                  (  0 <= i₁₅
                                                                    && i₁₅ < i₃₇ + 1
                                                                     ==> i₁₅ < N₃₁)))
                                                        &&   i₃₇ < N₃₁
                                                          ||   0 <= 0
                                                            && 0 <= N₃₁
                                                            && (forall x₂₀: int ::
                                                                  (x₂₀ == 0
                                                                     ==> (exists i₁₉: int ::
                                                                            i₁₉ < N₃₁
                                                                            && x₂₀ == 0
                                                                            && sum[0 := 0][x₂₀] == sum[0 := 0][0] + a₃₂[i₁₉])))
                                                            && (forall x₂₀: int ::
                                                                    x₂₀ == 0
                                                                    || sum[0 := 0][x₂₀] == sum[0 := 0][x₂₀])
                                                            && (forall i₁₉: int ::
                                                                  (  0 <= i₁₉
                                                                    && i₁₉ < 0
                                                                     ==> i₁₉ < N₃₁))
                                                            && (forall sum₃₈: [int]int, i₃₉: int ::
                                                                  (  0 <= i₃₉
                                                                    && i₃₉ <= N₃₁
                                                                    && (forall x₂₀: int ::
                                                                          (x₂₀ == 0
                                                                             ==> (exists i₁₉: int ::
                                                                                    i₁₉ < N₃₁
                                                                                    && x₂₀ == 0
                                                                                    && sum₃₈[x₂₀] == sum[0 := 0][0] + a₃₂[i₁₉])))
                                                                    && (forall x₂₀: int ::
                                                                            x₂₀ == 0
                                                                            || sum₃₈[x₂₀] == sum[0 := 0][x₂₀])
                                                                    && (forall i₁₉: int ::
                                                                          (  0 <= i₁₉
                                                                            && i₁₉ < i₃₉
                                                                             ==> i₁₉ < N₃₁))
                                                                     ==> (i₃₉ < N₃₁
                                                                         ==> 0 <= i₃₉ + 1
                                                                          && i₃₉ + 1 <= N₃₁
                                                                          && (forall x₂₀: int ::
                                                                                (x₂₀ == 0
                                                                                   ==> (exists i₁₉: int ::
                                                                                          i₁₉ < N₃₁
                                                                                          && x₂₀ == 0
                                                                                          && sum₃₈[0 := sum₃₈[0] + a₃₂[i₃₉]][x₂₀] == sum[0 := 0][0] + a₃₂[i₁₉])))
                                                                          && (forall x₂₀: int ::
                                                                                  x₂₀ == 0
                                                                                  || sum₃₈[0 := sum₃₈[0] + a₃₂[i₃₉]][x₂₀] == sum[0 := 0][x₂₀])
                                                                          && (forall i₁₉: int ::
                                                                                (  0 <= i₁₉
                                                                                  && i₁₉ < i₃₉ + 1
                                                                                   ==> i₁₉ < N₃₁)))
                                                                      &&   i₃₉ < N₃₁
                                                                        ||   0 <= 0
                                                                          && 0 <= N₃₁
                                                                          && (forall x₂₄: int ::
                                                                                (x₂₄ == 0
                                                                                   ==> (exists i₂₃: int ::
                                                                                          i₂₃ < N₃₁
                                                                                          && x₂₄ == 0
                                                                                          && sum₃₈[x₂₄] == sum₃₈[0] + b₃₄[i₂₃])))
                                                                          && (forall x₂₄: int ::
                                                                                  x₂₄ == 0
                                                                                  || sum₃₈[x₂₄] == sum₃₈[x₂₄])
                                                                          && (forall i₂₃: int ::
                                                                                (  0 <= i₂₃
                                                                                  && i₂₃ < 0
                                                                                   ==> i₂₃ < N₃₁))
                                                                          && (forall sum₄₀: [int]int, i₄₁: int ::
                                                                                (  0 <= i₄₁
                                                                                  && i₄₁ <= N₃₁
                                                                                  && (forall x₂₄: int ::
                                                                                        (x₂₄ == 0
                                                                                           ==> (exists i₂₃: int ::
                                                                                                  i₂₃ < N₃₁
                                                                                                  && x₂₄ == 0
                                                                                                  && sum₄₀[x₂₄] == sum₃₈[0] + b₃₄[i₂₃])))
                                                                                  && (forall x₂₄: int ::
                                                                                          x₂₄ == 0
                                                                                          || sum₄₀[x₂₄] == sum₃₈[x₂₄])
                                                                                  && (forall i₂₃: int ::
                                                                                        (  0 <= i₂₃
                                                                                          && i₂₃ < i₄₁
                                                                                           ==> i₂₃ < N₃₁))
                                                                                   ==> (i₄₁ < N₃₁
                                                                                       ==> 0 <= i₄₁ + 1
                                                                                        && i₄₁ + 1 <= N₃₁
                                                                                        && (forall x₂₄: int ::
                                                                                              (x₂₄ == 0
                                                                                                 ==> (exists i₂₃: int ::
                                                                                                        i₂₃ < N₃₁
                                                                                                        && x₂₄ == 0
                                                                                                        && sum₄₀[0 := sum₄₀[0] + b₃₄[i₄₁]][x₂₄] == sum₃₈[0] + b₃₄[i₂₃])))
                                                                                        && (forall x₂₄: int ::
                                                                                                x₂₄ == 0
                                                                                                || sum₄₀[0 := sum₄₀[0] + b₃₄[i₄₁]][x₂₄] == sum₃₈[x₂₄])
                                                                                        && (forall i₂₃: int ::
                                                                                              (  0 <= i₂₃
                                                                                                && i₂₃ < i₄₁ + 1
                                                                                                 ==> i₂₃ < N₃₁)))
                                                                                    &&   i₄₁ < N₃₁
                                                                                      ||   0 <= 0
                                                                                        && 0 <= N₃₁
                                                                                        && (forall x₂₈: int ::
                                                                                              (x₂₈ == 0
                                                                                                 ==> (exists i₂₇: int ::
                                                                                                        i₂₇ < N₃₁
                                                                                                        && x₂₈ == 0
                                                                                                        && sum₄₀[x₂₈] == sum₄₀[0] + c₃₆[i₂₇])))
                                                                                        && (forall x₂₈: int ::
                                                                                                x₂₈ == 0
                                                                                                || sum₄₀[x₂₈] == sum₄₀[x₂₈])
                                                                                        && (forall i₂₇: int ::
                                                                                              (  0 <= i₂₇
                                                                                                && i₂₇ < 0
                                                                                                 ==> i₂₇ < N₃₁))
                                                                                        && (forall sum₄₂: [int]int, i₄₃: int ::
                                                                                              (  0 <= i₄₃
                                                                                                && i₄₃ <= N₃₁
                                                                                                && (forall x₂₈: int ::
                                                                                                      (x₂₈ == 0
                                                                                                         ==> (exists i₂₇: int ::
                                                                                                                i₂₇ < N₃₁
                                                                                                                && x₂₈ == 0
                                                                                                                && sum₄₂[x₂₈] == sum₄₀[0] + c₃₆[i₂₇])))
                                                                                                && (forall x₂₈: int ::
                                                                                                        x₂₈ == 0
                                                                                                        || sum₄₂[x₂₈] == sum₄₀[x₂₈])
                                                                                                && (forall i₂₇: int ::
                                                                                                      (  0 <= i₂₇
                                                                                                        && i₂₇ < i₄₃
                                                                                                         ==> i₂₇ < N₃₁))
                                                                                                 ==> (i₄₃ < N₃₁
                                                                                                     ==> 0 <= i₄₃ + 1
                                                                                                      && i₄₃ + 1 <= N₃₁
                                                                                                      && (forall x₂₈: int ::
                                                                                                            (x₂₈ == 0
                                                                                                               ==> (exists i₂₇: int ::
                                                                                                                      i₂₇ < N₃₁
                                                                                                                      && x₂₈ == 0
                                                                                                                      && sum₄₂[0 := sum₄₂[0] + c₃₆[i₄₃]][x₂₈] == sum₄₀[0] + c₃₆[i₂₇])))
                                                                                                      && (forall x₂₈: int ::
                                                                                                              x₂₈ == 0
                                                                                                              || sum₄₂[0 := sum₄₂[0] + c₃₆[i₄₃]][x₂₈] == sum₄₀[x₂₈])
                                                                                                      && (forall i₂₇: int ::
                                                                                                            (  0 <= i₂₇
                                                                                                              && i₂₇ < i₄₃ + 1
                                                                                                               ==> i₂₇ < N₃₁)))
                                                                                                  &&   i₄₃ < N₃₁
                                                                                                    || sum₄₂[0] <= 3 * N₃₁)))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

goal (forall N₁₇: int ::
        N₁₇ <= 0
        || (forall sum: [int]int, a: [int]int ::
              (N₁₇ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₁₇
                  && (forall x₆: int, i₅: int ::
                        (  x₆ == i₅
                          && 0 <= i₅
                          && i₅ < 0
                           ==> (exists i₅: int ::
                                  i₅ < N₁₇
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
                           ==> i₅ < N₁₇))
                  && (forall a₁₈: [int]int, i₁₉: int ::
                        (  0 <= i₁₉
                          && i₁₉ <= N₁₇
                          && (forall x₆: int, i₅: int ::
                                (  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < i₁₉
                                   ==> (exists i₅: int ::
                                          i₅ < N₁₇
                                          && x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₉
                                          && a₁₈[x₆] == 1)))
                          && (forall x₆: int ::
                                  (exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₉)
                                  || a₁₈[x₆] == a[x₆])
                          && (forall i₅: int ::
                                (  0 <= i₅
                                  && i₅ < i₁₉
                                   ==> i₅ < N₁₇))
                           ==> (i₁₉ < N₁₇
                               ==> 0 <= i₁₉ + 1
                                && i₁₉ + 1 <= N₁₇
                                && (forall x₆: int, i₅: int ::
                                      (  x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₁₉ + 1
                                         ==> (exists i₅: int ::
                                                i₅ < N₁₇
                                                && x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₉ + 1
                                                && a₁₈[i₁₉ := 1][x₆] == 1)))
                                && (forall x₆: int ::
                                        (exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₉ + 1)
                                        || a₁₈[i₁₉ := 1][x₆] == a[x₆])
                                && (forall i₅: int ::
                                      (  0 <= i₅
                                        && i₅ < i₁₉ + 1
                                         ==> i₅ < N₁₇)))
                            &&   i₁₉ < N₁₇
                              ||   0 <= 0
                                && 0 <= N₁₇
                                && (forall x₁₀: int, i₉: int ::
                                      (  x₁₀ == i₉
                                        && 0 <= i₉
                                        && i₉ < 0
                                         ==> (exists i₉: int ::
                                                  a₁₈[i₉] == 1
                                                  && i₉ < N₁₇
                                                  && x₁₀ == i₉
                                                  && 0 <= i₉
                                                  && i₉ < 0
                                                  && a₁₈[x₁₀] == 5 + a₁₈[i₉])
                                          || (exists i₉: int ::
                                                (a₁₈[i₉] == 1
                                                   ==> false))))
                                && (forall x₁₀: int ::
                                        (exists i₉: int ::
                                                x₁₀ == i₉
                                                && 0 <= i₉
                                                && i₉ < 0)
                                        || a₁₈[x₁₀] == a₁₈[x₁₀])
                                && (forall i₉: int ::
                                      (  0 <= i₉
                                        && i₉ < 0
                                         ==> i₉ < N₁₇))
                                && (forall a₂₀: [int]int, i₂₁: int ::
                                      (  0 <= i₂₁
                                        && i₂₁ <= N₁₇
                                        && (forall x₁₀: int, i₉: int ::
                                              (  x₁₀ == i₉
                                                && 0 <= i₉
                                                && i₉ < i₂₁
                                                 ==> (exists i₉: int ::
                                                          a₂₀[i₉] == 1
                                                          && i₉ < N₁₇
                                                          && x₁₀ == i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₂₁
                                                          && a₂₀[x₁₀] == 5 + a₁₈[i₉])
                                                  || (exists i₉: int ::
                                                        (a₂₀[i₉] == 1
                                                           ==> false))))
                                        && (forall x₁₀: int ::
                                                (exists i₉: int ::
                                                        x₁₀ == i₉
                                                        && 0 <= i₉
                                                        && i₉ < i₂₁)
                                                || a₂₀[x₁₀] == a₁₈[x₁₀])
                                        && (forall i₉: int ::
                                              (  0 <= i₉
                                                && i₉ < i₂₁
                                                 ==> i₉ < N₁₇))
                                         ==> (i₂₁ < N₁₇
                                             ==> (a₂₀[i₂₁] == 1
                                                 ==> 0 <= i₂₁ + 1
                                                  && i₂₁ + 1 <= N₁₇
                                                  && (forall x₁₀: int, i₉: int ::
                                                        (  x₁₀ == i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₂₁ + 1
                                                           ==> (exists i₉: int ::
                                                                    a₂₀[i₂₁ := a₂₀[i₂₁] + 5][i₉] == 1
                                                                    && i₉ < N₁₇
                                                                    && x₁₀ == i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₂₁ + 1
                                                                    && a₂₀[i₂₁ := a₂₀[i₂₁] + 5][x₁₀] == 5 + a₁₈[i₉])
                                                            || (exists i₉: int ::
                                                                  (a₂₀[i₂₁ := a₂₀[i₂₁] + 5][i₉] == 1
                                                                     ==> false))))
                                                  && (forall x₁₀: int ::
                                                          (exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₂₁ + 1)
                                                          || a₂₀[i₂₁ := a₂₀[i₂₁] + 5][x₁₀] == a₁₈[x₁₀])
                                                  && (forall i₉: int ::
                                                        (  0 <= i₉
                                                          && i₉ < i₂₁ + 1
                                                           ==> i₉ < N₁₇)))
                                              &&   a₂₀[i₂₁] == 1
                                                ||   0 <= i₂₁ + 1
                                                  && i₂₁ + 1 <= N₁₇
                                                  && (forall x₁₀: int, i₉: int ::
                                                        (  x₁₀ == i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₂₁ + 1
                                                           ==> (exists i₉: int ::
                                                                    a₂₀[i₂₁ := a₂₀[i₂₁] - 1][i₉] == 1
                                                                    && i₉ < N₁₇
                                                                    && x₁₀ == i₉
                                                                    && 0 <= i₉
                                                                    && i₉ < i₂₁ + 1
                                                                    && a₂₀[i₂₁ := a₂₀[i₂₁] - 1][x₁₀] == 5 + a₁₈[i₉])
                                                            || (exists i₉: int ::
                                                                  (a₂₀[i₂₁ := a₂₀[i₂₁] - 1][i₉] == 1
                                                                     ==> false))))
                                                  && (forall x₁₀: int ::
                                                          (exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₂₁ + 1)
                                                          || a₂₀[i₂₁ := a₂₀[i₂₁] - 1][x₁₀] == a₁₈[x₁₀])
                                                  && (forall i₉: int ::
                                                        (  0 <= i₉
                                                          && i₉ < i₂₁ + 1
                                                           ==> i₉ < N₁₇)))
                                          &&   i₂₁ < N₁₇
                                            ||   0 <= 0
                                              && 0 <= N₁₇
                                              && (forall x₁₄: int ::
                                                    (x₁₄ == 0
                                                       ==> (exists i₁₃: int ::
                                                                a₂₀[i₁₃] == 6
                                                                && i₁₃ < N₁₇
                                                                && x₁₄ == 0
                                                                && sum[0 := 1][x₁₄] == sum[0 := 1][0] + a₂₀[i₁₃])
                                                        || (exists i₁₃: int ::
                                                              (a₂₀[i₁₃] == 6
                                                                 ==> false))))
                                              && (forall x₁₄: int ::
                                                      x₁₄ == 0
                                                      || sum[0 := 1][x₁₄] == sum[0 := 1][x₁₄])
                                              && (forall i₁₃: int ::
                                                    (  0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> i₁₃ < N₁₇))
                                              && (forall sum₂₂: [int]int, i₂₃: int ::
                                                    (  0 <= i₂₃
                                                      && i₂₃ <= N₁₇
                                                      && (forall x₁₄: int ::
                                                            (x₁₄ == 0
                                                               ==> (exists i₁₃: int ::
                                                                        a₂₀[i₁₃] == 6
                                                                        && i₁₃ < N₁₇
                                                                        && x₁₄ == 0
                                                                        && sum₂₂[x₁₄] == sum[0 := 1][0] + a₂₀[i₁₃])
                                                                || (exists i₁₃: int ::
                                                                      (a₂₀[i₁₃] == 6
                                                                         ==> false))))
                                                      && (forall x₁₄: int ::
                                                              x₁₄ == 0
                                                              || sum₂₂[x₁₄] == sum[0 := 1][x₁₄])
                                                      && (forall i₁₃: int ::
                                                            (  0 <= i₁₃
                                                              && i₁₃ < i₂₃
                                                               ==> i₁₃ < N₁₇))
                                                       ==> (i₂₃ < N₁₇
                                                           ==> (a₂₀[i₂₃] == 6
                                                               ==> 0 <= i₂₃ + 1
                                                                && i₂₃ + 1 <= N₁₇
                                                                && (forall x₁₄: int ::
                                                                      (x₁₄ == 0
                                                                         ==> (exists i₁₃: int ::
                                                                                  a₂₀[i₁₃] == 6
                                                                                  && i₁₃ < N₁₇
                                                                                  && x₁₄ == 0
                                                                                  && sum₂₂[0 := sum₂₂[0] + a₂₀[i₂₃]][x₁₄] == sum[0 := 1][0] + a₂₀[i₁₃])
                                                                          || (exists i₁₃: int ::
                                                                                (a₂₀[i₁₃] == 6
                                                                                   ==> false))))
                                                                && (forall x₁₄: int ::
                                                                        x₁₄ == 0
                                                                        || sum₂₂[0 := sum₂₂[0] + a₂₀[i₂₃]][x₁₄] == sum[0 := 1][x₁₄])
                                                                && (forall i₁₃: int ::
                                                                      (  0 <= i₁₃
                                                                        && i₁₃ < i₂₃ + 1
                                                                         ==> i₁₃ < N₁₇)))
                                                            &&   a₂₀[i₂₃] == 6
                                                              ||   0 <= i₂₃ + 1
                                                                && i₂₃ + 1 <= N₁₇
                                                                && (forall x₁₄: int ::
                                                                      (x₁₄ == 0
                                                                         ==> (exists i₁₃: int ::
                                                                                  a₂₀[i₁₃] == 6
                                                                                  && i₁₃ < N₁₇
                                                                                  && x₁₄ == 0
                                                                                  && sum₂₂[0 := sum₂₂[0] * a₂₀[i₂₃]][x₁₄] == sum[0 := 1][0] + a₂₀[i₁₃])
                                                                          || (exists i₁₃: int ::
                                                                                (a₂₀[i₁₃] == 6
                                                                                   ==> false))))
                                                                && (forall x₁₄: int ::
                                                                        x₁₄ == 0
                                                                        || sum₂₂[0 := sum₂₂[0] * a₂₀[i₂₃]][x₁₄] == sum[0 := 1][x₁₄])
                                                                && (forall i₁₃: int ::
                                                                      (  0 <= i₁₃
                                                                        && i₁₃ < i₂₃ + 1
                                                                         ==> i₁₃ < N₁₇)))
                                                        &&   i₂₃ < N₁₇
                                                          || sum₂₂[0] == 6 * N₁₇)))))))));


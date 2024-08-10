data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

goal (forall N₁₃: int ::
        N₁₃ <= 0
        || (forall sum: [int]int, a: [int]int ::
              (N₁₃ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₁₃
                  && (forall x₆: int, i₅: int ::
                        (  x₆ == i₅
                          && 0 <= i₅
                          && i₅ < 0
                           ==> (exists i₅: int ::
                                  i₅ < N₁₃
                                  && x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0
                                  && a[x₆] == i₅ % 4)))
                  && (forall x₆: int ::
                          (exists i₅: int ::
                                  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                          || a[x₆] == a[x₆])
                  && (forall i₅: int ::
                        (  0 <= i₅
                          && i₅ < 0
                           ==> i₅ < N₁₃))
                  && (forall a₁₄: [int]int, i₁₅: int ::
                        (  0 <= i₁₅
                          && i₁₅ <= N₁₃
                          && (forall x₆: int, i₅: int ::
                                (  x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < i₁₅
                                   ==> (exists i₅: int ::
                                          i₅ < N₁₃
                                          && x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₅
                                          && a₁₄[x₆] == i₅ % 4)))
                          && (forall x₆: int ::
                                  (exists i₅: int ::
                                          x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₅)
                                  || a₁₄[x₆] == a[x₆])
                          && (forall i₅: int ::
                                (  0 <= i₅
                                  && i₅ < i₁₅
                                   ==> i₅ < N₁₃))
                           ==> (i₁₅ < N₁₃
                               ==> 0 <= i₁₅ + 1
                                && i₁₅ + 1 <= N₁₃
                                && (forall x₆: int, i₅: int ::
                                      (  x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₁₅ + 1
                                         ==> (exists i₅: int ::
                                                i₅ < N₁₃
                                                && x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₅ + 1
                                                && a₁₄[i₁₅ := i₁₅ % 4][x₆] == i₅ % 4)))
                                && (forall x₆: int ::
                                        (exists i₅: int ::
                                                x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₁₅ + 1)
                                        || a₁₄[i₁₅ := i₁₅ % 4][x₆] == a[x₆])
                                && (forall i₅: int ::
                                      (  0 <= i₅
                                        && i₅ < i₁₅ + 1
                                         ==> i₅ < N₁₃)))
                            &&   i₁₅ < N₁₃
                              ||   0 <= 0
                                && 0 <= N₁₃
                                && (forall x₁₀: int ::
                                      (x₁₀ == 0
                                         ==> (exists i₉: int ::
                                                  i₉ == 0
                                                  && i₉ < N₁₃
                                                  && x₁₀ == 0
                                                  && sum[x₁₀] == 0)
                                          || (exists i₉: int ::
                                                (i₉ == 0
                                                   ==> false))))
                                && (forall x₁₀: int ::
                                        x₁₀ == 0
                                        || sum[x₁₀] == sum[x₁₀])
                                && (forall i₉: int ::
                                      (  0 <= i₉
                                        && i₉ < 0
                                         ==> i₉ < N₁₃))
                                && (forall sum₁₆: [int]int, i₁₇: int ::
                                      (  0 <= i₁₇
                                        && i₁₇ <= N₁₃
                                        && (forall x₁₀: int ::
                                              (x₁₀ == 0
                                                 ==> (exists i₉: int ::
                                                          i₉ == 0
                                                          && i₉ < N₁₃
                                                          && x₁₀ == 0
                                                          && sum₁₆[x₁₀] == 0)
                                                  || (exists i₉: int ::
                                                        (i₉ == 0
                                                           ==> false))))
                                        && (forall x₁₀: int ::
                                                x₁₀ == 0
                                                || sum₁₆[x₁₀] == sum[x₁₀])
                                        && (forall i₉: int ::
                                              (  0 <= i₉
                                                && i₉ < i₁₇
                                                 ==> i₉ < N₁₃))
                                         ==> (i₁₇ < N₁₃
                                             ==> (i₁₇ == 0
                                                 ==> 0 <= i₁₇ + 1
                                                  && i₁₇ + 1 <= N₁₃
                                                  && (forall x₁₀: int ::
                                                        (x₁₀ == 0
                                                           ==> (exists i₉: int ::
                                                                    i₉ == 0
                                                                    && i₉ < N₁₃
                                                                    && x₁₀ == 0
                                                                    && sum₁₆[0 := 0][x₁₀] == 0)
                                                            || (exists i₉: int ::
                                                                  (i₉ == 0
                                                                     ==> false))))
                                                  && (forall x₁₀: int ::
                                                          x₁₀ == 0
                                                          || sum₁₆[0 := 0][x₁₀] == sum[x₁₀])
                                                  && (forall i₉: int ::
                                                        (  0 <= i₉
                                                          && i₉ < i₁₇ + 1
                                                           ==> i₉ < N₁₃)))
                                              &&   i₁₇ == 0
                                                ||   0 <= i₁₇ + 1
                                                  && i₁₇ + 1 <= N₁₃
                                                  && (forall x₁₀: int ::
                                                        (x₁₀ == 0
                                                           ==> (exists i₉: int ::
                                                                    i₉ == 0
                                                                    && i₉ < N₁₃
                                                                    && x₁₀ == 0
                                                                    && sum₁₆[0 := sum₁₆[0] + a₁₄[i₁₇]][x₁₀] == 0)
                                                            || (exists i₉: int ::
                                                                  (i₉ == 0
                                                                     ==> false))))
                                                  && (forall x₁₀: int ::
                                                          x₁₀ == 0
                                                          || sum₁₆[0 := sum₁₆[0] + a₁₄[i₁₇]][x₁₀] == sum[x₁₀])
                                                  && (forall i₉: int ::
                                                        (  0 <= i₉
                                                          && i₉ < i₁₇ + 1
                                                           ==> i₉ < N₁₃)))
                                          &&   i₁₇ < N₁₃
                                            || sum₁₆[0] <= 3 * N₁₃)))))));


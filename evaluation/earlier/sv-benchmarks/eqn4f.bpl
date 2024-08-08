data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

goal (forall N₁₅: int ::
        N₁₅ <= 0
        || (forall a: [int]int, b: [int]int ::
              (N₁₅ <= 2147483647 / 4
                 ==> 1 <= 1
                  && 1 <= N₁₅
                  && (forall x₆: int, i₅: int ::
                        (  x₆ == i₅
                          && 1 <= i₅
                          && i₅ < 1
                           ==> (exists i₅: int ::
                                  i₅ < N₁₅
                                  && x₆ == i₅
                                  && 1 <= i₅
                                  && i₅ < 1
                                  && a[0 := 8][x₆] == 8 + a[0 := 8][-1 + i₅])))
                  && (forall x₆: int ::
                          (exists i₅: int ::
                                  x₆ == i₅
                                  && 1 <= i₅
                                  && i₅ < 1)
                          || a[0 := 8][x₆] == a[0 := 8][x₆])
                  && (forall i₅: int ::
                        (  1 <= i₅
                          && i₅ < 1
                           ==> i₅ < N₁₅))
                  && (forall a₁₆: [int]int, i₁₇: int ::
                        (  1 <= i₁₇
                          && i₁₇ <= N₁₅
                          && (forall x₆: int, i₅: int ::
                                (  x₆ == i₅
                                  && 1 <= i₅
                                  && i₅ < i₁₇
                                   ==> (exists i₅: int ::
                                          i₅ < N₁₅
                                          && x₆ == i₅
                                          && 1 <= i₅
                                          && i₅ < i₁₇
                                          && a₁₆[x₆] == 8 + a[0 := 8][-1 + i₅])))
                          && (forall x₆: int ::
                                  (exists i₅: int ::
                                          x₆ == i₅
                                          && 1 <= i₅
                                          && i₅ < i₁₇)
                                  || a₁₆[x₆] == a[0 := 8][x₆])
                          && (forall i₅: int ::
                                (  1 <= i₅
                                  && i₅ < i₁₇
                                   ==> i₅ < N₁₅))
                           ==> (i₁₇ < N₁₅
                               ==> 1 <= i₁₇ + 1
                                && i₁₇ + 1 <= N₁₅
                                && (forall x₆: int, i₅: int ::
                                      (  x₆ == i₅
                                        && 1 <= i₅
                                        && i₅ < i₁₇ + 1
                                         ==> (exists i₅: int ::
                                                i₅ < N₁₅
                                                && x₆ == i₅
                                                && 1 <= i₅
                                                && i₅ < i₁₇ + 1
                                                && a₁₆[i₁₇ := a₁₆[i₁₇ - 1] + 8][x₆] == 8 + a[0 := 8][-1 + i₅])))
                                && (forall x₆: int ::
                                        (exists i₅: int ::
                                                x₆ == i₅
                                                && 1 <= i₅
                                                && i₅ < i₁₇ + 1)
                                        || a₁₆[i₁₇ := a₁₆[i₁₇ - 1] + 8][x₆] == a[0 := 8][x₆])
                                && (forall i₅: int ::
                                      (  1 <= i₅
                                        && i₅ < i₁₇ + 1
                                         ==> i₅ < N₁₅)))
                            &&   i₁₇ < N₁₅
                              ||   1 <= 1
                                && 1 <= N₁₅
                                && (forall x₁₀: int, i₉: int ::
                                      (  x₁₀ == i₉
                                        && 1 <= i₉
                                        && i₉ < 1
                                         ==> (exists i₉: int ::
                                                i₉ < N₁₅
                                                && x₁₀ == i₉
                                                && 1 <= i₉
                                                && i₉ < 1
                                                && b[0 := 0][x₁₀] == b[0 := 0][-1 + i₉] + a₁₆[-1 + i₉])))
                                && (forall x₁₀: int ::
                                        (exists i₉: int ::
                                                x₁₀ == i₉
                                                && 1 <= i₉
                                                && i₉ < 1)
                                        || b[0 := 0][x₁₀] == b[0 := 0][x₁₀])
                                && (forall i₉: int ::
                                      (  1 <= i₉
                                        && i₉ < 1
                                         ==> i₉ < N₁₅))
                                && (forall b₁₈: [int]int, i₁₉: int ::
                                      (  1 <= i₁₉
                                        && i₁₉ <= N₁₅
                                        && (forall x₁₀: int, i₉: int ::
                                              (  x₁₀ == i₉
                                                && 1 <= i₉
                                                && i₉ < i₁₉
                                                 ==> (exists i₉: int ::
                                                        i₉ < N₁₅
                                                        && x₁₀ == i₉
                                                        && 1 <= i₉
                                                        && i₉ < i₁₉
                                                        && b₁₈[x₁₀] == b[0 := 0][-1 + i₉] + a₁₆[-1 + i₉])))
                                        && (forall x₁₀: int ::
                                                (exists i₉: int ::
                                                        x₁₀ == i₉
                                                        && 1 <= i₉
                                                        && i₉ < i₁₉)
                                                || b₁₈[x₁₀] == b[0 := 0][x₁₀])
                                        && (forall i₉: int ::
                                              (  1 <= i₉
                                                && i₉ < i₁₉
                                                 ==> i₉ < N₁₅))
                                         ==> (i₁₉ < N₁₅
                                             ==> 1 <= i₁₉ + 1
                                              && i₁₉ + 1 <= N₁₅
                                              && (forall x₁₀: int, i₉: int ::
                                                    (  x₁₀ == i₉
                                                      && 1 <= i₉
                                                      && i₉ < i₁₉ + 1
                                                       ==> (exists i₉: int ::
                                                              i₉ < N₁₅
                                                              && x₁₀ == i₉
                                                              && 1 <= i₉
                                                              && i₉ < i₁₉ + 1
                                                              && b₁₈[i₁₉ := b₁₈[i₁₉ - 1] + a₁₆[i₁₉ - 1]][x₁₀] == b[0 := 0][-1 + i₉] + a₁₆[-1 + i₉])))
                                              && (forall x₁₀: int ::
                                                      (exists i₉: int ::
                                                              x₁₀ == i₉
                                                              && 1 <= i₉
                                                              && i₉ < i₁₉ + 1)
                                                      || b₁₈[i₁₉ := b₁₈[i₁₉ - 1] + a₁₆[i₁₉ - 1]][x₁₀] == b[0 := 0][x₁₀])
                                              && (forall i₉: int ::
                                                    (  1 <= i₉
                                                      && i₉ < i₁₉ + 1
                                                       ==> i₉ < N₁₅)))
                                          &&   i₁₉ < N₁₅
                                            ||   0 <= 0
                                              && 0 <= N₁₅
                                              && (forall i₁₃: int ::
                                                    (  0 <= i₁₃
                                                      && i₁₃ < 0
                                                       ==> i₁₃ < N₁₅))
                                              && (forall i₂₀: int ::
                                                    (  0 <= i₂₀
                                                      && i₂₀ <= N₁₅
                                                      && (forall i₁₃: int ::
                                                            (  0 <= i₁₃
                                                              && i₁₃ < i₂₀
                                                               ==> i₁₃ < N₁₅))
                                                       ==> (i₂₀ < N₁₅
                                                         ==> b₁₈[i₂₀] == 4 * i₂₀ * i₂₀ + 4 * i₂₀ + 1
                                                          && 0 <= i₂₀ + 1
                                                          && i₂₀ + 1 <= N₁₅
                                                          && (forall i₁₃: int ::
                                                                (  0 <= i₁₃
                                                                  && i₁₃ < i₂₀ + 1
                                                                   ==> i₁₃ < N₁₅))))))))))));


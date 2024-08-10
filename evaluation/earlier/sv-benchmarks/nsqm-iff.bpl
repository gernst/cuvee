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
                 ==> 0 <= 0
                  && 0 <= N₁₅
                  && (forall x₆: int, i₅: int ::
                        (  x₆ == 0
                          && x₆ == i₅
                          && 0 <= i₅
                          && i₅ < 0
                           ==> (exists i₅: int ::
                                    i₅ == 0
                                    && i₅ < N₁₅
                                    && x₆ == 0
                                    && b[x₆] == 1)
                            || (exists i₅: int ::
                                  (i₅ == 0
                                     ==> false))))
                  && (forall x₆: int ::
                          (exists i₅: int ::
                                  x₆ == 0
                                  && x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < 0)
                          || b[x₆] == b[x₆])
                  && (forall i₅: int ::
                        (  0 <= i₅
                          && i₅ < 0
                           ==> i₅ < N₁₅))
                  && (forall b₁₆: [int]int, i₁₇: int ::
                        (  0 <= i₁₇
                          && i₁₇ <= N₁₅
                          && (forall x₆: int, i₅: int ::
                                (  x₆ == 0
                                  && x₆ == i₅
                                  && 0 <= i₅
                                  && i₅ < i₁₇
                                   ==> (exists i₅: int ::
                                            i₅ == 0
                                            && i₅ < N₁₅
                                            && x₆ == 0
                                            && b₁₆[x₆] == 1)
                                    || (exists i₅: int ::
                                          (i₅ == 0
                                             ==> false))))
                          && (forall x₆: int ::
                                  (exists i₅: int ::
                                          x₆ == 0
                                          && x₆ == i₅
                                          && 0 <= i₅
                                          && i₅ < i₁₇)
                                  || b₁₆[x₆] == b[x₆])
                          && (forall i₅: int ::
                                (  0 <= i₅
                                  && i₅ < i₁₇
                                   ==> i₅ < N₁₅))
                           ==> (i₁₇ < N₁₅
                               ==> (i₁₇ == 0
                                   ==> 0 <= i₁₇ + 1
                                    && i₁₇ + 1 <= N₁₅
                                    && (forall x₆: int, i₅: int ::
                                          (  x₆ == 0
                                            && x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₁₇ + 1
                                             ==> (exists i₅: int ::
                                                      i₅ == 0
                                                      && i₅ < N₁₅
                                                      && x₆ == 0
                                                      && b₁₆[0 := 1][x₆] == 1)
                                              || (exists i₅: int ::
                                                    (i₅ == 0
                                                       ==> false))))
                                    && (forall x₆: int ::
                                            (exists i₅: int ::
                                                    x₆ == 0
                                                    && x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₁₇ + 1)
                                            || b₁₆[0 := 1][x₆] == b[x₆])
                                    && (forall i₅: int ::
                                          (  0 <= i₅
                                            && i₅ < i₁₇ + 1
                                             ==> i₅ < N₁₅)))
                                &&   i₁₇ == 0
                                  ||   0 <= i₁₇ + 1
                                    && i₁₇ + 1 <= N₁₅
                                    && (forall x₆: int, i₅: int ::
                                          (  x₆ == 0
                                            && x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₁₇ + 1
                                             ==> (exists i₅: int ::
                                                      i₅ == 0
                                                      && i₅ < N₁₅
                                                      && x₆ == 0
                                                      && b₁₆[i₁₇ := b₁₆[i₁₇ - 1] + 2][x₆] == 1)
                                              || (exists i₅: int ::
                                                    (i₅ == 0
                                                       ==> false))))
                                    && (forall x₆: int ::
                                            (exists i₅: int ::
                                                    x₆ == 0
                                                    && x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₁₇ + 1)
                                            || b₁₆[i₁₇ := b₁₆[i₁₇ - 1] + 2][x₆] == b[x₆])
                                    && (forall i₅: int ::
                                          (  0 <= i₅
                                            && i₅ < i₁₇ + 1
                                             ==> i₅ < N₁₅)))
                            &&   i₁₇ < N₁₅
                              ||   0 <= 0
                                && 0 <= N₁₅
                                && (forall x₁₀: int, i₉: int ::
                                      (  x₁₀ == 0
                                        && x₁₀ == i₉
                                        && 0 <= i₉
                                        && i₉ < 0
                                         ==> (exists i₉: int ::
                                                  i₉ == 0
                                                  && i₉ < N₁₅
                                                  && x₁₀ == 0
                                                  && a[x₁₀] == 1 + N₁₅)
                                          || (exists i₉: int ::
                                                (i₉ == 0
                                                   ==> false))))
                                && (forall x₁₀: int ::
                                        (exists i₉: int ::
                                                x₁₀ == 0
                                                && x₁₀ == i₉
                                                && 0 <= i₉
                                                && i₉ < 0)
                                        || a[x₁₀] == a[x₁₀])
                                && (forall i₉: int ::
                                      (  0 <= i₉
                                        && i₉ < 0
                                         ==> i₉ < N₁₅))
                                && (forall a₁₈: [int]int, i₁₉: int ::
                                      (  0 <= i₁₉
                                        && i₁₉ <= N₁₅
                                        && (forall x₁₀: int, i₉: int ::
                                              (  x₁₀ == 0
                                                && x₁₀ == i₉
                                                && 0 <= i₉
                                                && i₉ < i₁₉
                                                 ==> (exists i₉: int ::
                                                          i₉ == 0
                                                          && i₉ < N₁₅
                                                          && x₁₀ == 0
                                                          && a₁₈[x₁₀] == 1 + N₁₅)
                                                  || (exists i₉: int ::
                                                        (i₉ == 0
                                                           ==> false))))
                                        && (forall x₁₀: int ::
                                                (exists i₉: int ::
                                                        x₁₀ == 0
                                                        && x₁₀ == i₉
                                                        && 0 <= i₉
                                                        && i₉ < i₁₉)
                                                || a₁₈[x₁₀] == a[x₁₀])
                                        && (forall i₉: int ::
                                              (  0 <= i₉
                                                && i₉ < i₁₉
                                                 ==> i₉ < N₁₅))
                                         ==> (i₁₉ < N₁₅
                                             ==> (i₁₉ == 0
                                                 ==> 0 <= i₁₉ + 1
                                                  && i₁₉ + 1 <= N₁₅
                                                  && (forall x₁₀: int, i₉: int ::
                                                        (  x₁₀ == 0
                                                          && x₁₀ == i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₁₉ + 1
                                                           ==> (exists i₉: int ::
                                                                    i₉ == 0
                                                                    && i₉ < N₁₅
                                                                    && x₁₀ == 0
                                                                    && a₁₈[0 := N₁₅ + 1][x₁₀] == 1 + N₁₅)
                                                            || (exists i₉: int ::
                                                                  (i₉ == 0
                                                                     ==> false))))
                                                  && (forall x₁₀: int ::
                                                          (exists i₉: int ::
                                                                  x₁₀ == 0
                                                                  && x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₁₉ + 1)
                                                          || a₁₈[0 := N₁₅ + 1][x₁₀] == a[x₁₀])
                                                  && (forall i₉: int ::
                                                        (  0 <= i₉
                                                          && i₉ < i₁₉ + 1
                                                           ==> i₉ < N₁₅)))
                                              &&   i₁₉ == 0
                                                ||   0 <= i₁₉ + 1
                                                  && i₁₉ + 1 <= N₁₅
                                                  && (forall x₁₀: int, i₉: int ::
                                                        (  x₁₀ == 0
                                                          && x₁₀ == i₉
                                                          && 0 <= i₉
                                                          && i₉ < i₁₉ + 1
                                                           ==> (exists i₉: int ::
                                                                    i₉ == 0
                                                                    && i₉ < N₁₅
                                                                    && x₁₀ == 0
                                                                    && a₁₈[i₁₉ := a₁₈[i₁₉ - 1] + b₁₆[i₁₉ - 1] + 2][x₁₀] == 1 + N₁₅)
                                                            || (exists i₉: int ::
                                                                  (i₉ == 0
                                                                     ==> false))))
                                                  && (forall x₁₀: int ::
                                                          (exists i₉: int ::
                                                                  x₁₀ == 0
                                                                  && x₁₀ == i₉
                                                                  && 0 <= i₉
                                                                  && i₉ < i₁₉ + 1)
                                                          || a₁₈[i₁₉ := a₁₈[i₁₉ - 1] + b₁₆[i₁₉ - 1] + 2][x₁₀] == a[x₁₀])
                                                  && (forall i₉: int ::
                                                        (  0 <= i₉
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
                                                         ==> a₁₈[i₂₀] == (i₂₀ + 1) * (i₂₀ + 1)
                                                          && 0 <= i₂₀ + 1
                                                          && i₂₀ + 1 <= N₁₅
                                                          && (forall i₁₃: int ::
                                                                (  0 <= i₁₃
                                                                  && i₁₃ < i₂₀ + 1
                                                                   ==> i₁₃ < N₁₅))))))))))));


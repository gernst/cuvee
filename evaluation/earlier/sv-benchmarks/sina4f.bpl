data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₄: int ::
        N₂₄ <= 0
        || (forall sum: [int]int, a: [int]int, b: [int]int ::
              (N₂₄ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₂₄
                  && (forall x₇: int, i₆: int ::
                        (  x₇ == i₆
                          && 0 <= i₆
                          && i₆ < 0
                           ==> (exists i₆: int ::
                                  i₆ < N₂₄
                                  && x₇ == i₆
                                  && 0 <= i₆
                                  && i₆ < 0
                                  && a[x₇] == 1)))
                  && (forall x₇: int ::
                          (exists i₆: int ::
                                  x₇ == i₆
                                  && 0 <= i₆
                                  && i₆ < 0)
                          || a[x₇] == a[x₇])
                  && (forall i₆: int ::
                        (  0 <= i₆
                          && i₆ < 0
                           ==> i₆ < N₂₄))
                  && (forall a₂₅: [int]int, i₂₆: int ::
                        (  0 <= i₂₆
                          && i₂₆ <= N₂₄
                          && (forall x₇: int, i₆: int ::
                                (  x₇ == i₆
                                  && 0 <= i₆
                                  && i₆ < i₂₆
                                   ==> (exists i₆: int ::
                                          i₆ < N₂₄
                                          && x₇ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₂₆
                                          && a₂₅[x₇] == 1)))
                          && (forall x₇: int ::
                                  (exists i₆: int ::
                                          x₇ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₂₆)
                                  || a₂₅[x₇] == a[x₇])
                          && (forall i₆: int ::
                                (  0 <= i₆
                                  && i₆ < i₂₆
                                   ==> i₆ < N₂₄))
                           ==> (i₂₆ < N₂₄
                               ==> 0 <= i₂₆ + 1
                                && i₂₆ + 1 <= N₂₄
                                && (forall x₇: int, i₆: int ::
                                      (  x₇ == i₆
                                        && 0 <= i₆
                                        && i₆ < i₂₆ + 1
                                         ==> (exists i₆: int ::
                                                i₆ < N₂₄
                                                && x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₂₆ + 1
                                                && a₂₅[i₂₆ := 1][x₇] == 1)))
                                && (forall x₇: int ::
                                        (exists i₆: int ::
                                                x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₂₆ + 1)
                                        || a₂₅[i₂₆ := 1][x₇] == a[x₇])
                                && (forall i₆: int ::
                                      (  0 <= i₆
                                        && i₆ < i₂₆ + 1
                                         ==> i₆ < N₂₄)))
                            &&   i₂₆ < N₂₄
                              ||   0 <= 0
                                && 0 <= N₂₄
                                && (forall x₁₁: int ::
                                      (x₁₁ == 0
                                         ==> (exists i₁₀: int ::
                                                i₁₀ < N₂₄
                                                && x₁₁ == 0
                                                && sum[0 := 0][x₁₁] == sum[0 := 0][0] + a₂₅[i₁₀])))
                                && (forall x₁₁: int ::
                                        x₁₁ == 0
                                        || sum[0 := 0][x₁₁] == sum[0 := 0][x₁₁])
                                && (forall i₁₀: int ::
                                      (  0 <= i₁₀
                                        && i₁₀ < 0
                                         ==> i₁₀ < N₂₄))
                                && (forall sum₂₇: [int]int, i₂₈: int ::
                                      (  0 <= i₂₈
                                        && i₂₈ <= N₂₄
                                        && (forall x₁₁: int ::
                                              (x₁₁ == 0
                                                 ==> (exists i₁₀: int ::
                                                        i₁₀ < N₂₄
                                                        && x₁₁ == 0
                                                        && sum₂₇[x₁₁] == sum[0 := 0][0] + a₂₅[i₁₀])))
                                        && (forall x₁₁: int ::
                                                x₁₁ == 0
                                                || sum₂₇[x₁₁] == sum[0 := 0][x₁₁])
                                        && (forall i₁₀: int ::
                                              (  0 <= i₁₀
                                                && i₁₀ < i₂₈
                                                 ==> i₁₀ < N₂₄))
                                         ==> (i₂₈ < N₂₄
                                             ==> 0 <= i₂₈ + 1
                                              && i₂₈ + 1 <= N₂₄
                                              && (forall x₁₁: int ::
                                                    (x₁₁ == 0
                                                       ==> (exists i₁₀: int ::
                                                              i₁₀ < N₂₄
                                                              && x₁₁ == 0
                                                              && sum₂₇[0 := sum₂₇[0] + a₂₅[i₂₈]][x₁₁] == sum[0 := 0][0] + a₂₅[i₁₀])))
                                              && (forall x₁₁: int ::
                                                      x₁₁ == 0
                                                      || sum₂₇[0 := sum₂₇[0] + a₂₅[i₂₈]][x₁₁] == sum[0 := 0][x₁₁])
                                              && (forall i₁₀: int ::
                                                    (  0 <= i₁₀
                                                      && i₁₀ < i₂₈ + 1
                                                       ==> i₁₀ < N₂₄)))
                                          &&   i₂₈ < N₂₄
                                            ||   0 <= 0
                                              && 0 <= N₂₄
                                              && (forall x₁₅: int, i₁₄: int ::
                                                    (  x₁₅ == i₁₄
                                                      && 0 <= i₁₄
                                                      && i₁₄ < 0
                                                       ==> (exists i₁₄: int ::
                                                              i₁₄ < N₂₄
                                                              && x₁₅ == i₁₄
                                                              && 0 <= i₁₄
                                                              && i₁₄ < 0
                                                              && a₂₅[x₁₅] == a₂₅[i₁₄] + sum₂₇[0])))
                                              && (forall x₁₅: int ::
                                                      (exists i₁₄: int ::
                                                              x₁₅ == i₁₄
                                                              && 0 <= i₁₄
                                                              && i₁₄ < 0)
                                                      || a₂₅[x₁₅] == a₂₅[x₁₅])
                                              && (forall i₁₄: int ::
                                                    (  0 <= i₁₄
                                                      && i₁₄ < 0
                                                       ==> i₁₄ < N₂₄))
                                              && (forall a₂₉: [int]int, i₃₀: int ::
                                                    (  0 <= i₃₀
                                                      && i₃₀ <= N₂₄
                                                      && (forall x₁₅: int, i₁₄: int ::
                                                            (  x₁₅ == i₁₄
                                                              && 0 <= i₁₄
                                                              && i₁₄ < i₃₀
                                                               ==> (exists i₁₄: int ::
                                                                      i₁₄ < N₂₄
                                                                      && x₁₅ == i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < i₃₀
                                                                      && a₂₉[x₁₅] == a₂₅[i₁₄] + sum₂₇[0])))
                                                      && (forall x₁₅: int ::
                                                              (exists i₁₄: int ::
                                                                      x₁₅ == i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < i₃₀)
                                                              || a₂₉[x₁₅] == a₂₅[x₁₅])
                                                      && (forall i₁₄: int ::
                                                            (  0 <= i₁₄
                                                              && i₁₄ < i₃₀
                                                               ==> i₁₄ < N₂₄))
                                                       ==> (i₃₀ < N₂₄
                                                           ==> 0 <= i₃₀ + 1
                                                            && i₃₀ + 1 <= N₂₄
                                                            && (forall x₁₅: int, i₁₄: int ::
                                                                  (  x₁₅ == i₁₄
                                                                    && 0 <= i₁₄
                                                                    && i₁₄ < i₃₀ + 1
                                                                     ==> (exists i₁₄: int ::
                                                                            i₁₄ < N₂₄
                                                                            && x₁₅ == i₁₄
                                                                            && 0 <= i₁₄
                                                                            && i₁₄ < i₃₀ + 1
                                                                            && a₂₉[i₃₀ := a₂₉[i₃₀] + sum₂₇[0]][x₁₅] == a₂₅[i₁₄] + sum₂₇[0])))
                                                            && (forall x₁₅: int ::
                                                                    (exists i₁₄: int ::
                                                                            x₁₅ == i₁₄
                                                                            && 0 <= i₁₄
                                                                            && i₁₄ < i₃₀ + 1)
                                                                    || a₂₉[i₃₀ := a₂₉[i₃₀] + sum₂₇[0]][x₁₅] == a₂₅[x₁₅])
                                                            && (forall i₁₄: int ::
                                                                  (  0 <= i₁₄
                                                                    && i₁₄ < i₃₀ + 1
                                                                     ==> i₁₄ < N₂₄)))
                                                        &&   i₃₀ < N₂₄
                                                          ||   0 <= 0
                                                            && 0 <= N₂₄
                                                            && (forall x₁₉: int, i₁₈: int ::
                                                                  (  x₁₉ == i₁₈
                                                                    && 0 <= i₁₈
                                                                    && i₁₈ < 0
                                                                     ==> (exists i₁₈: int ::
                                                                            i₁₈ < N₂₄
                                                                            && x₁₉ == i₁₈
                                                                            && 0 <= i₁₈
                                                                            && i₁₈ < 0
                                                                            && b[x₁₉] == 1 + a₂₉[i₁₈])))
                                                            && (forall x₁₉: int ::
                                                                    (exists i₁₈: int ::
                                                                            x₁₉ == i₁₈
                                                                            && 0 <= i₁₈
                                                                            && i₁₈ < 0)
                                                                    || b[x₁₉] == b[x₁₉])
                                                            && (forall i₁₈: int ::
                                                                  (  0 <= i₁₈
                                                                    && i₁₈ < 0
                                                                     ==> i₁₈ < N₂₄))
                                                            && (forall b₃₁: [int]int, i₃₂: int ::
                                                                  (  0 <= i₃₂
                                                                    && i₃₂ <= N₂₄
                                                                    && (forall x₁₉: int, i₁₈: int ::
                                                                          (  x₁₉ == i₁₈
                                                                            && 0 <= i₁₈
                                                                            && i₁₈ < i₃₂
                                                                             ==> (exists i₁₈: int ::
                                                                                    i₁₈ < N₂₄
                                                                                    && x₁₉ == i₁₈
                                                                                    && 0 <= i₁₈
                                                                                    && i₁₈ < i₃₂
                                                                                    && b₃₁[x₁₉] == 1 + a₂₉[i₁₈])))
                                                                    && (forall x₁₉: int ::
                                                                            (exists i₁₈: int ::
                                                                                    x₁₉ == i₁₈
                                                                                    && 0 <= i₁₈
                                                                                    && i₁₈ < i₃₂)
                                                                            || b₃₁[x₁₉] == b[x₁₉])
                                                                    && (forall i₁₈: int ::
                                                                          (  0 <= i₁₈
                                                                            && i₁₈ < i₃₂
                                                                             ==> i₁₈ < N₂₄))
                                                                     ==> (i₃₂ < N₂₄
                                                                         ==> 0 <= i₃₂ + 1
                                                                          && i₃₂ + 1 <= N₂₄
                                                                          && (forall x₁₉: int, i₁₈: int ::
                                                                                (  x₁₉ == i₁₈
                                                                                  && 0 <= i₁₈
                                                                                  && i₁₈ < i₃₂ + 1
                                                                                   ==> (exists i₁₈: int ::
                                                                                          i₁₈ < N₂₄
                                                                                          && x₁₉ == i₁₈
                                                                                          && 0 <= i₁₈
                                                                                          && i₁₈ < i₃₂ + 1
                                                                                          && b₃₁[i₃₂ := a₂₉[i₃₂] + 1][x₁₉] == 1 + a₂₉[i₁₈])))
                                                                          && (forall x₁₉: int ::
                                                                                  (exists i₁₈: int ::
                                                                                          x₁₉ == i₁₈
                                                                                          && 0 <= i₁₈
                                                                                          && i₁₈ < i₃₂ + 1)
                                                                                  || b₃₁[i₃₂ := a₂₉[i₃₂] + 1][x₁₉] == b[x₁₉])
                                                                          && (forall i₁₈: int ::
                                                                                (  0 <= i₁₈
                                                                                  && i₁₈ < i₃₂ + 1
                                                                                   ==> i₁₈ < N₂₄)))
                                                                      &&   i₃₂ < N₂₄
                                                                        ||   0 <= 0
                                                                          && 0 <= N₂₄
                                                                          && (forall i₂₂: int ::
                                                                                (  0 <= i₂₂
                                                                                  && i₂₂ < 0
                                                                                   ==> i₂₂ < N₂₄))
                                                                          && (forall i₃₃: int ::
                                                                                (  0 <= i₃₃
                                                                                  && i₃₃ <= N₂₄
                                                                                  && (forall i₂₂: int ::
                                                                                        (  0 <= i₂₂
                                                                                          && i₂₂ < i₃₃
                                                                                           ==> i₂₂ < N₂₄))
                                                                                   ==> (i₃₃ < N₂₄
                                                                                     ==> b₃₁[i₃₃] == N₂₄
                                                                                      && 0 <= i₃₃ + 1
                                                                                      && i₃₃ + 1 <= N₂₄
                                                                                      && (forall i₂₂: int ::
                                                                                            (  0 <= i₂₂
                                                                                              && i₂₂ < i₃₃ + 1
                                                                                               ==> i₂₂ < N₂₄))))))))))))))));


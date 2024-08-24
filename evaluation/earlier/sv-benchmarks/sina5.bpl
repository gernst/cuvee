data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₈: int ::
        N₂₈ <= 0
        || (forall sum: [int]int, a: [int]int, b: [int]int ::
              (N₂₈ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₂₈
                  && (forall x₇: int, i₆: int ::
                        (  x₇ == i₆
                          && 0 <= i₆
                          && i₆ < 0
                           ==> (exists i₆: int ::
                                  i₆ < N₂₈
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
                           ==> i₆ < N₂₈))
                  && (forall a₂₉: [int]int, i₃₀: int ::
                        (  0 <= i₃₀
                          && i₃₀ <= N₂₈
                          && (forall x₇: int, i₆: int ::
                                (  x₇ == i₆
                                  && 0 <= i₆
                                  && i₆ < i₃₀
                                   ==> (exists i₆: int ::
                                          i₆ < N₂₈
                                          && x₇ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₃₀
                                          && a₂₉[x₇] == 1)))
                          && (forall x₇: int ::
                                  (exists i₆: int ::
                                          x₇ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₃₀)
                                  || a₂₉[x₇] == a[x₇])
                          && (forall i₆: int ::
                                (  0 <= i₆
                                  && i₆ < i₃₀
                                   ==> i₆ < N₂₈))
                           ==> (i₃₀ < N₂₈
                               ==> 0 <= i₃₀ + 1
                                && i₃₀ + 1 <= N₂₈
                                && (forall x₇: int, i₆: int ::
                                      (  x₇ == i₆
                                        && 0 <= i₆
                                        && i₆ < i₃₀ + 1
                                         ==> (exists i₆: int ::
                                                i₆ < N₂₈
                                                && x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₃₀ + 1
                                                && a₂₉[i₃₀ := 1][x₇] == 1)))
                                && (forall x₇: int ::
                                        (exists i₆: int ::
                                                x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₃₀ + 1)
                                        || a₂₉[i₃₀ := 1][x₇] == a[x₇])
                                && (forall i₆: int ::
                                      (  0 <= i₆
                                        && i₆ < i₃₀ + 1
                                         ==> i₆ < N₂₈)))
                            &&   i₃₀ < N₂₈
                              ||   0 <= 0
                                && 0 <= N₂₈
                                && (forall x₁₁: int, i₁₀: int ::
                                      (  x₁₁ == i₁₀
                                        && 0 <= i₁₀
                                        && i₁₀ < 0
                                         ==> (exists i₁₀: int ::
                                                i₁₀ < N₂₈
                                                && x₁₁ == i₁₀
                                                && 0 <= i₁₀
                                                && i₁₀ < 0
                                                && b[x₁₁] == 1)))
                                && (forall x₁₁: int ::
                                        (exists i₁₀: int ::
                                                x₁₁ == i₁₀
                                                && 0 <= i₁₀
                                                && i₁₀ < 0)
                                        || b[x₁₁] == b[x₁₁])
                                && (forall i₁₀: int ::
                                      (  0 <= i₁₀
                                        && i₁₀ < 0
                                         ==> i₁₀ < N₂₈))
                                && (forall b₃₁: [int]int, i₃₂: int ::
                                      (  0 <= i₃₂
                                        && i₃₂ <= N₂₈
                                        && (forall x₁₁: int, i₁₀: int ::
                                              (  x₁₁ == i₁₀
                                                && 0 <= i₁₀
                                                && i₁₀ < i₃₂
                                                 ==> (exists i₁₀: int ::
                                                        i₁₀ < N₂₈
                                                        && x₁₁ == i₁₀
                                                        && 0 <= i₁₀
                                                        && i₁₀ < i₃₂
                                                        && b₃₁[x₁₁] == 1)))
                                        && (forall x₁₁: int ::
                                                (exists i₁₀: int ::
                                                        x₁₁ == i₁₀
                                                        && 0 <= i₁₀
                                                        && i₁₀ < i₃₂)
                                                || b₃₁[x₁₁] == b[x₁₁])
                                        && (forall i₁₀: int ::
                                              (  0 <= i₁₀
                                                && i₁₀ < i₃₂
                                                 ==> i₁₀ < N₂₈))
                                         ==> (i₃₂ < N₂₈
                                             ==> 0 <= i₃₂ + 1
                                              && i₃₂ + 1 <= N₂₈
                                              && (forall x₁₁: int, i₁₀: int ::
                                                    (  x₁₁ == i₁₀
                                                      && 0 <= i₁₀
                                                      && i₁₀ < i₃₂ + 1
                                                       ==> (exists i₁₀: int ::
                                                              i₁₀ < N₂₈
                                                              && x₁₁ == i₁₀
                                                              && 0 <= i₁₀
                                                              && i₁₀ < i₃₂ + 1
                                                              && b₃₁[i₃₂ := 1][x₁₁] == 1)))
                                              && (forall x₁₁: int ::
                                                      (exists i₁₀: int ::
                                                              x₁₁ == i₁₀
                                                              && 0 <= i₁₀
                                                              && i₁₀ < i₃₂ + 1)
                                                      || b₃₁[i₃₂ := 1][x₁₁] == b[x₁₁])
                                              && (forall i₁₀: int ::
                                                    (  0 <= i₁₀
                                                      && i₁₀ < i₃₂ + 1
                                                       ==> i₁₀ < N₂₈)))
                                          &&   i₃₂ < N₂₈
                                            ||   0 <= 0
                                              && 0 <= N₂₈
                                              && (forall x₁₅: int ::
                                                    (x₁₅ == 0
                                                       ==> (exists i₁₄: int ::
                                                              i₁₄ < N₂₈
                                                              && x₁₅ == 0
                                                              && sum[0 := 0][x₁₅] == sum[0 := 0][0] + a₂₉[i₁₄])))
                                              && (forall x₁₅: int ::
                                                      x₁₅ == 0
                                                      || sum[0 := 0][x₁₅] == sum[0 := 0][x₁₅])
                                              && (forall i₁₄: int ::
                                                    (  0 <= i₁₄
                                                      && i₁₄ < 0
                                                       ==> i₁₄ < N₂₈))
                                              && (forall sum₃₃: [int]int, i₃₄: int ::
                                                    (  0 <= i₃₄
                                                      && i₃₄ <= N₂₈
                                                      && (forall x₁₅: int ::
                                                            (x₁₅ == 0
                                                               ==> (exists i₁₄: int ::
                                                                      i₁₄ < N₂₈
                                                                      && x₁₅ == 0
                                                                      && sum₃₃[x₁₅] == sum[0 := 0][0] + a₂₉[i₁₄])))
                                                      && (forall x₁₅: int ::
                                                              x₁₅ == 0
                                                              || sum₃₃[x₁₅] == sum[0 := 0][x₁₅])
                                                      && (forall i₁₄: int ::
                                                            (  0 <= i₁₄
                                                              && i₁₄ < i₃₄
                                                               ==> i₁₄ < N₂₈))
                                                       ==> (i₃₄ < N₂₈
                                                           ==> 0 <= i₃₄ + 1
                                                            && i₃₄ + 1 <= N₂₈
                                                            && (forall x₁₅: int ::
                                                                  (x₁₅ == 0
                                                                     ==> (exists i₁₄: int ::
                                                                            i₁₄ < N₂₈
                                                                            && x₁₅ == 0
                                                                            && sum₃₃[0 := sum₃₃[0] + a₂₉[i₃₄]][x₁₅] == sum[0 := 0][0] + a₂₉[i₁₄])))
                                                            && (forall x₁₅: int ::
                                                                    x₁₅ == 0
                                                                    || sum₃₃[0 := sum₃₃[0] + a₂₉[i₃₄]][x₁₅] == sum[0 := 0][x₁₅])
                                                            && (forall i₁₄: int ::
                                                                  (  0 <= i₁₄
                                                                    && i₁₄ < i₃₄ + 1
                                                                     ==> i₁₄ < N₂₈)))
                                                        &&   i₃₄ < N₂₈
                                                          ||   0 <= 0
                                                            && 0 <= N₂₈
                                                            && (forall x₁₉: int ::
                                                                  (x₁₉ == 0
                                                                     ==> (exists i₁₈: int ::
                                                                            i₁₈ < N₂₈
                                                                            && x₁₉ == 0
                                                                            && sum₃₃[x₁₉] == b₃₁[i₁₈] + sum₃₃[0])))
                                                            && (forall x₁₉: int ::
                                                                    x₁₉ == 0
                                                                    || sum₃₃[x₁₉] == sum₃₃[x₁₉])
                                                            && (forall i₁₈: int ::
                                                                  (  0 <= i₁₈
                                                                    && i₁₈ < 0
                                                                     ==> i₁₈ < N₂₈))
                                                            && (forall sum₃₅: [int]int, i₃₆: int ::
                                                                  (  0 <= i₃₆
                                                                    && i₃₆ <= N₂₈
                                                                    && (forall x₁₉: int ::
                                                                          (x₁₉ == 0
                                                                             ==> (exists i₁₈: int ::
                                                                                    i₁₈ < N₂₈
                                                                                    && x₁₉ == 0
                                                                                    && sum₃₅[x₁₉] == b₃₁[i₁₈] + sum₃₃[0])))
                                                                    && (forall x₁₉: int ::
                                                                            x₁₉ == 0
                                                                            || sum₃₅[x₁₉] == sum₃₃[x₁₉])
                                                                    && (forall i₁₈: int ::
                                                                          (  0 <= i₁₈
                                                                            && i₁₈ < i₃₆
                                                                             ==> i₁₈ < N₂₈))
                                                                     ==> (i₃₆ < N₂₈
                                                                         ==> 0 <= i₃₆ + 1
                                                                          && i₃₆ + 1 <= N₂₈
                                                                          && (forall x₁₉: int ::
                                                                                (x₁₉ == 0
                                                                                   ==> (exists i₁₈: int ::
                                                                                          i₁₈ < N₂₈
                                                                                          && x₁₉ == 0
                                                                                          && sum₃₅[0 := sum₃₅[0] + b₃₁[i₃₆]][x₁₉] == b₃₁[i₁₈] + sum₃₃[0])))
                                                                          && (forall x₁₉: int ::
                                                                                  x₁₉ == 0
                                                                                  || sum₃₅[0 := sum₃₅[0] + b₃₁[i₃₆]][x₁₉] == sum₃₃[x₁₉])
                                                                          && (forall i₁₈: int ::
                                                                                (  0 <= i₁₈
                                                                                  && i₁₈ < i₃₆ + 1
                                                                                   ==> i₁₈ < N₂₈)))
                                                                      &&   i₃₆ < N₂₈
                                                                        ||   0 <= 0
                                                                          && 0 <= N₂₈
                                                                          && (forall x₂₃: int, i₂₂: int ::
                                                                                (  x₂₃ == i₂₂
                                                                                  && 0 <= i₂₂
                                                                                  && i₂₂ < 0
                                                                                   ==> (exists i₂₂: int ::
                                                                                          i₂₂ < N₂₈
                                                                                          && x₂₃ == i₂₂
                                                                                          && 0 <= i₂₂
                                                                                          && i₂₂ < 0
                                                                                          && a₂₉[x₂₃] == sum₃₅[0] + a₂₉[i₂₂])))
                                                                          && (forall x₂₃: int ::
                                                                                  (exists i₂₂: int ::
                                                                                          x₂₃ == i₂₂
                                                                                          && 0 <= i₂₂
                                                                                          && i₂₂ < 0)
                                                                                  || a₂₉[x₂₃] == a₂₉[x₂₃])
                                                                          && (forall i₂₂: int ::
                                                                                (  0 <= i₂₂
                                                                                  && i₂₂ < 0
                                                                                   ==> i₂₂ < N₂₈))
                                                                          && (forall a₃₇: [int]int, i₃₈: int ::
                                                                                (  0 <= i₃₈
                                                                                  && i₃₈ <= N₂₈
                                                                                  && (forall x₂₃: int, i₂₂: int ::
                                                                                        (  x₂₃ == i₂₂
                                                                                          && 0 <= i₂₂
                                                                                          && i₂₂ < i₃₈
                                                                                           ==> (exists i₂₂: int ::
                                                                                                  i₂₂ < N₂₈
                                                                                                  && x₂₃ == i₂₂
                                                                                                  && 0 <= i₂₂
                                                                                                  && i₂₂ < i₃₈
                                                                                                  && a₃₇[x₂₃] == sum₃₅[0] + a₂₉[i₂₂])))
                                                                                  && (forall x₂₃: int ::
                                                                                          (exists i₂₂: int ::
                                                                                                  x₂₃ == i₂₂
                                                                                                  && 0 <= i₂₂
                                                                                                  && i₂₂ < i₃₈)
                                                                                          || a₃₇[x₂₃] == a₂₉[x₂₃])
                                                                                  && (forall i₂₂: int ::
                                                                                        (  0 <= i₂₂
                                                                                          && i₂₂ < i₃₈
                                                                                           ==> i₂₂ < N₂₈))
                                                                                   ==> (i₃₈ < N₂₈
                                                                                       ==> 0 <= i₃₈ + 1
                                                                                        && i₃₈ + 1 <= N₂₈
                                                                                        && (forall x₂₃: int, i₂₂: int ::
                                                                                              (  x₂₃ == i₂₂
                                                                                                && 0 <= i₂₂
                                                                                                && i₂₂ < i₃₈ + 1
                                                                                                 ==> (exists i₂₂: int ::
                                                                                                        i₂₂ < N₂₈
                                                                                                        && x₂₃ == i₂₂
                                                                                                        && 0 <= i₂₂
                                                                                                        && i₂₂ < i₃₈ + 1
                                                                                                        && a₃₇[i₃₈ := a₃₇[i₃₈] + sum₃₅[0]][x₂₃] == sum₃₅[0] + a₂₉[i₂₂])))
                                                                                        && (forall x₂₃: int ::
                                                                                                (exists i₂₂: int ::
                                                                                                        x₂₃ == i₂₂
                                                                                                        && 0 <= i₂₂
                                                                                                        && i₂₂ < i₃₈ + 1)
                                                                                                || a₃₇[i₃₈ := a₃₇[i₃₈] + sum₃₅[0]][x₂₃] == a₂₉[x₂₃])
                                                                                        && (forall i₂₂: int ::
                                                                                              (  0 <= i₂₂
                                                                                                && i₂₂ < i₃₈ + 1
                                                                                                 ==> i₂₂ < N₂₈)))
                                                                                    &&   i₃₈ < N₂₈
                                                                                      ||   0 <= 0
                                                                                        && 0 <= N₂₈
                                                                                        && (forall i₂₆: int ::
                                                                                              (  0 <= i₂₆
                                                                                                && i₂₆ < 0
                                                                                                 ==> i₂₆ < N₂₈))
                                                                                        && (forall i₃₉: int ::
                                                                                              (  0 <= i₃₉
                                                                                                && i₃₉ <= N₂₈
                                                                                                && (forall i₂₆: int ::
                                                                                                      (  0 <= i₂₆
                                                                                                        && i₂₆ < i₃₉
                                                                                                         ==> i₂₆ < N₂₈))
                                                                                                 ==> (i₃₉ < N₂₈
                                                                                                   ==> a₃₇[i₃₉] == 2 * N₂₈ + 1
                                                                                                    && 0 <= i₃₉ + 1
                                                                                                    && i₃₉ + 1 <= N₂₈
                                                                                                    && (forall i₂₆: int ::
                                                                                                          (  0 <= i₂₆
                                                                                                            && i₂₆ < i₃₉ + 1
                                                                                                             ==> i₂₆ < N₂₈))))))))))))))))));


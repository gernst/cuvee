data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

goal (forall N₂₂: int ::
        N₂₂ <= 0
        || (forall sum: [int]int, a: [int]int, b: [int]int ::
              (N₂₂ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₂₂
                  && (forall x₇: int, i₆: int ::
                        (  x₇ == i₆
                          && 0 <= i₆
                          && i₆ < 0
                           ==> (exists i₆: int ::
                                  i₆ < N₂₂
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
                           ==> i₆ < N₂₂))
                  && (forall a₂₃: [int]int, i₂₄: int ::
                        (  0 <= i₂₄
                          && i₂₄ <= N₂₂
                          && (forall x₇: int, i₆: int ::
                                (  x₇ == i₆
                                  && 0 <= i₆
                                  && i₆ < i₂₄
                                   ==> (exists i₆: int ::
                                          i₆ < N₂₂
                                          && x₇ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₂₄
                                          && a₂₃[x₇] == 1)))
                          && (forall x₇: int ::
                                  (exists i₆: int ::
                                          x₇ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₂₄)
                                  || a₂₃[x₇] == a[x₇])
                          && (forall i₆: int ::
                                (  0 <= i₆
                                  && i₆ < i₂₄
                                   ==> i₆ < N₂₂))
                           ==> (i₂₄ < N₂₂
                               ==> 0 <= i₂₄ + 1
                                && i₂₄ + 1 <= N₂₂
                                && (forall x₇: int, i₆: int ::
                                      (  x₇ == i₆
                                        && 0 <= i₆
                                        && i₆ < i₂₄ + 1
                                         ==> (exists i₆: int ::
                                                i₆ < N₂₂
                                                && x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₂₄ + 1
                                                && a₂₃[i₂₄ := 1][x₇] == 1)))
                                && (forall x₇: int ::
                                        (exists i₆: int ::
                                                x₇ == i₆
                                                && 0 <= i₆
                                                && i₆ < i₂₄ + 1)
                                        || a₂₃[i₂₄ := 1][x₇] == a[x₇])
                                && (forall i₆: int ::
                                      (  0 <= i₆
                                        && i₆ < i₂₄ + 1
                                         ==> i₆ < N₂₂)))
                            &&   i₂₄ < N₂₂
                              ||   0 <= 0
                                && 0 <= N₂₂
                                && (forall x₁₁: int, i₁₀: int ::
                                      (  x₁₁ == i₁₀
                                        && 0 <= i₁₀
                                        && i₁₀ < 0
                                         ==> (exists i₁₀: int ::
                                                i₁₀ < N₂₂
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
                                         ==> i₁₀ < N₂₂))
                                && (forall b₂₅: [int]int, i₂₆: int ::
                                      (  0 <= i₂₆
                                        && i₂₆ <= N₂₂
                                        && (forall x₁₁: int, i₁₀: int ::
                                              (  x₁₁ == i₁₀
                                                && 0 <= i₁₀
                                                && i₁₀ < i₂₆
                                                 ==> (exists i₁₀: int ::
                                                        i₁₀ < N₂₂
                                                        && x₁₁ == i₁₀
                                                        && 0 <= i₁₀
                                                        && i₁₀ < i₂₆
                                                        && b₂₅[x₁₁] == 1)))
                                        && (forall x₁₁: int ::
                                                (exists i₁₀: int ::
                                                        x₁₁ == i₁₀
                                                        && 0 <= i₁₀
                                                        && i₁₀ < i₂₆)
                                                || b₂₅[x₁₁] == b[x₁₁])
                                        && (forall i₁₀: int ::
                                              (  0 <= i₁₀
                                                && i₁₀ < i₂₆
                                                 ==> i₁₀ < N₂₂))
                                         ==> (i₂₆ < N₂₂
                                             ==> 0 <= i₂₆ + 1
                                              && i₂₆ + 1 <= N₂₂
                                              && (forall x₁₁: int, i₁₀: int ::
                                                    (  x₁₁ == i₁₀
                                                      && 0 <= i₁₀
                                                      && i₁₀ < i₂₆ + 1
                                                       ==> (exists i₁₀: int ::
                                                              i₁₀ < N₂₂
                                                              && x₁₁ == i₁₀
                                                              && 0 <= i₁₀
                                                              && i₁₀ < i₂₆ + 1
                                                              && b₂₅[i₂₆ := 1][x₁₁] == 1)))
                                              && (forall x₁₁: int ::
                                                      (exists i₁₀: int ::
                                                              x₁₁ == i₁₀
                                                              && 0 <= i₁₀
                                                              && i₁₀ < i₂₆ + 1)
                                                      || b₂₅[i₂₆ := 1][x₁₁] == b[x₁₁])
                                              && (forall i₁₀: int ::
                                                    (  0 <= i₁₀
                                                      && i₁₀ < i₂₆ + 1
                                                       ==> i₁₀ < N₂₂)))
                                          &&   i₂₆ < N₂₂
                                            ||   0 <= 0
                                              && 0 <= N₂₂
                                              && (forall x₁₅: int ::
                                                    (x₁₅ == 0
                                                       ==> (exists i₁₄: int ::
                                                              i₁₄ < N₂₂
                                                              && x₁₅ == 0
                                                              && sum[0 := 0][x₁₅] == sum[0 := 0][0] + a₂₃[i₁₄])))
                                              && (forall x₁₅: int ::
                                                      x₁₅ == 0
                                                      || sum[0 := 0][x₁₅] == sum[0 := 0][x₁₅])
                                              && (forall i₁₄: int ::
                                                    (  0 <= i₁₄
                                                      && i₁₄ < 0
                                                       ==> i₁₄ < N₂₂))
                                              && (forall sum₂₇: [int]int, i₂₈: int ::
                                                    (  0 <= i₂₈
                                                      && i₂₈ <= N₂₂
                                                      && (forall x₁₅: int ::
                                                            (x₁₅ == 0
                                                               ==> (exists i₁₄: int ::
                                                                      i₁₄ < N₂₂
                                                                      && x₁₅ == 0
                                                                      && sum₂₇[x₁₅] == sum[0 := 0][0] + a₂₃[i₁₄])))
                                                      && (forall x₁₅: int ::
                                                              x₁₅ == 0
                                                              || sum₂₇[x₁₅] == sum[0 := 0][x₁₅])
                                                      && (forall i₁₄: int ::
                                                            (  0 <= i₁₄
                                                              && i₁₄ < i₂₈
                                                               ==> i₁₄ < N₂₂))
                                                       ==> (i₂₈ < N₂₂
                                                           ==> 0 <= i₂₈ + 1
                                                            && i₂₈ + 1 <= N₂₂
                                                            && (forall x₁₅: int ::
                                                                  (x₁₅ == 0
                                                                     ==> (exists i₁₄: int ::
                                                                            i₁₄ < N₂₂
                                                                            && x₁₅ == 0
                                                                            && sum₂₇[0 := sum₂₇[0] + a₂₃[i₂₈]][x₁₅] == sum[0 := 0][0] + a₂₃[i₁₄])))
                                                            && (forall x₁₅: int ::
                                                                    x₁₅ == 0
                                                                    || sum₂₇[0 := sum₂₇[0] + a₂₃[i₂₈]][x₁₅] == sum[0 := 0][x₁₅])
                                                            && (forall i₁₄: int ::
                                                                  (  0 <= i₁₄
                                                                    && i₁₄ < i₂₈ + 1
                                                                     ==> i₁₄ < N₂₂)))
                                                        &&   i₂₈ < N₂₂
                                                          ||   0 <= 0
                                                            && 0 <= N₂₂
                                                            && (forall x₁₉: int ::
                                                                  (x₁₉ == 0
                                                                     ==> (exists i₁₈: int ::
                                                                            i₁₈ < N₂₂
                                                                            && x₁₉ == 0
                                                                            && sum₂₇[x₁₉] == b₂₅[i₁₈] + sum₂₇[0])))
                                                            && (forall x₁₉: int ::
                                                                    x₁₉ == 0
                                                                    || sum₂₇[x₁₉] == sum₂₇[x₁₉])
                                                            && (forall i₁₈: int ::
                                                                  (  0 <= i₁₈
                                                                    && i₁₈ < 0
                                                                     ==> i₁₈ < N₂₂))
                                                            && (forall sum₂₉: [int]int, i₃₀: int ::
                                                                  (  0 <= i₃₀
                                                                    && i₃₀ <= N₂₂
                                                                    && (forall x₁₉: int ::
                                                                          (x₁₉ == 0
                                                                             ==> (exists i₁₈: int ::
                                                                                    i₁₈ < N₂₂
                                                                                    && x₁₉ == 0
                                                                                    && sum₂₉[x₁₉] == b₂₅[i₁₈] + sum₂₇[0])))
                                                                    && (forall x₁₉: int ::
                                                                            x₁₉ == 0
                                                                            || sum₂₉[x₁₉] == sum₂₇[x₁₉])
                                                                    && (forall i₁₈: int ::
                                                                          (  0 <= i₁₈
                                                                            && i₁₈ < i₃₀
                                                                             ==> i₁₈ < N₂₂))
                                                                     ==> (i₃₀ < N₂₂
                                                                         ==> 0 <= i₃₀ + 1
                                                                          && i₃₀ + 1 <= N₂₂
                                                                          && (forall x₁₉: int ::
                                                                                (x₁₉ == 0
                                                                                   ==> (exists i₁₈: int ::
                                                                                          i₁₈ < N₂₂
                                                                                          && x₁₉ == 0
                                                                                          && sum₂₉[0 := sum₂₉[0] + b₂₅[i₃₀]][x₁₉] == b₂₅[i₁₈] + sum₂₇[0])))
                                                                          && (forall x₁₉: int ::
                                                                                  x₁₉ == 0
                                                                                  || sum₂₉[0 := sum₂₉[0] + b₂₅[i₃₀]][x₁₉] == sum₂₇[x₁₉])
                                                                          && (forall i₁₈: int ::
                                                                                (  0 <= i₁₈
                                                                                  && i₁₈ < i₃₀ + 1
                                                                                   ==> i₁₈ < N₂₂)))
                                                                      &&   i₃₀ < N₂₂
                                                                        || sum₂₉[0] <= 2 * N₂₂)))))))))));


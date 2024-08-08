data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var N: int;

goal (forall N₂₀: int ::
        N₂₀ <= 0
        || (forall a: [int]int, b: [int]int, c: [int]int ::
              (N₂₀ <= 2147483647 / 4
                 ==> 1 <= 1
                  && 1 <= N₂₀
                  && (forall x₇: int, i₆: int ::
                        (  x₇ == i₆
                          && 1 <= i₆
                          && i₆ < 1
                           ==> (exists i₆: int ::
                                  i₆ < N₂₀
                                  && x₇ == i₆
                                  && 1 <= i₆
                                  && i₆ < 1
                                  && a[0 := 6][x₇] == 6 + a[0 := 6][-1 + i₆])))
                  && (forall x₇: int ::
                          (exists i₆: int ::
                                  x₇ == i₆
                                  && 1 <= i₆
                                  && i₆ < 1)
                          || a[0 := 6][x₇] == a[0 := 6][x₇])
                  && (forall i₆: int ::
                        (  1 <= i₆
                          && i₆ < 1
                           ==> i₆ < N₂₀))
                  && (forall a₂₁: [int]int, i₂₂: int ::
                        (  1 <= i₂₂
                          && i₂₂ <= N₂₀
                          && (forall x₇: int, i₆: int ::
                                (  x₇ == i₆
                                  && 1 <= i₆
                                  && i₆ < i₂₂
                                   ==> (exists i₆: int ::
                                          i₆ < N₂₀
                                          && x₇ == i₆
                                          && 1 <= i₆
                                          && i₆ < i₂₂
                                          && a₂₁[x₇] == 6 + a[0 := 6][-1 + i₆])))
                          && (forall x₇: int ::
                                  (exists i₆: int ::
                                          x₇ == i₆
                                          && 1 <= i₆
                                          && i₆ < i₂₂)
                                  || a₂₁[x₇] == a[0 := 6][x₇])
                          && (forall i₆: int ::
                                (  1 <= i₆
                                  && i₆ < i₂₂
                                   ==> i₆ < N₂₀))
                           ==> (i₂₂ < N₂₀
                               ==> 1 <= i₂₂ + 1
                                && i₂₂ + 1 <= N₂₀
                                && (forall x₇: int, i₆: int ::
                                      (  x₇ == i₆
                                        && 1 <= i₆
                                        && i₆ < i₂₂ + 1
                                         ==> (exists i₆: int ::
                                                i₆ < N₂₀
                                                && x₇ == i₆
                                                && 1 <= i₆
                                                && i₆ < i₂₂ + 1
                                                && a₂₁[i₂₂ := a₂₁[i₂₂ - 1] + 6][x₇] == 6 + a[0 := 6][-1 + i₆])))
                                && (forall x₇: int ::
                                        (exists i₆: int ::
                                                x₇ == i₆
                                                && 1 <= i₆
                                                && i₆ < i₂₂ + 1)
                                        || a₂₁[i₂₂ := a₂₁[i₂₂ - 1] + 6][x₇] == a[0 := 6][x₇])
                                && (forall i₆: int ::
                                      (  1 <= i₆
                                        && i₆ < i₂₂ + 1
                                         ==> i₆ < N₂₀)))
                            &&   i₂₂ < N₂₀
                              ||   1 <= 1
                                && 1 <= N₂₀
                                && (forall x₁₁: int, i₁₀: int ::
                                      (  x₁₁ == i₁₀
                                        && 1 <= i₁₀
                                        && i₁₀ < 1
                                         ==> (exists i₁₀: int ::
                                                i₁₀ < N₂₀
                                                && x₁₁ == i₁₀
                                                && 1 <= i₁₀
                                                && i₁₀ < 1
                                                && b[0 := 1][x₁₁] == b[0 := 1][-1 + i₁₀] + a₂₁[-1 + i₁₀])))
                                && (forall x₁₁: int ::
                                        (exists i₁₀: int ::
                                                x₁₁ == i₁₀
                                                && 1 <= i₁₀
                                                && i₁₀ < 1)
                                        || b[0 := 1][x₁₁] == b[0 := 1][x₁₁])
                                && (forall i₁₀: int ::
                                      (  1 <= i₁₀
                                        && i₁₀ < 1
                                         ==> i₁₀ < N₂₀))
                                && (forall b₂₃: [int]int, i₂₄: int ::
                                      (  1 <= i₂₄
                                        && i₂₄ <= N₂₀
                                        && (forall x₁₁: int, i₁₀: int ::
                                              (  x₁₁ == i₁₀
                                                && 1 <= i₁₀
                                                && i₁₀ < i₂₄
                                                 ==> (exists i₁₀: int ::
                                                        i₁₀ < N₂₀
                                                        && x₁₁ == i₁₀
                                                        && 1 <= i₁₀
                                                        && i₁₀ < i₂₄
                                                        && b₂₃[x₁₁] == b[0 := 1][-1 + i₁₀] + a₂₁[-1 + i₁₀])))
                                        && (forall x₁₁: int ::
                                                (exists i₁₀: int ::
                                                        x₁₁ == i₁₀
                                                        && 1 <= i₁₀
                                                        && i₁₀ < i₂₄)
                                                || b₂₃[x₁₁] == b[0 := 1][x₁₁])
                                        && (forall i₁₀: int ::
                                              (  1 <= i₁₀
                                                && i₁₀ < i₂₄
                                                 ==> i₁₀ < N₂₀))
                                         ==> (i₂₄ < N₂₀
                                             ==> 1 <= i₂₄ + 1
                                              && i₂₄ + 1 <= N₂₀
                                              && (forall x₁₁: int, i₁₀: int ::
                                                    (  x₁₁ == i₁₀
                                                      && 1 <= i₁₀
                                                      && i₁₀ < i₂₄ + 1
                                                       ==> (exists i₁₀: int ::
                                                              i₁₀ < N₂₀
                                                              && x₁₁ == i₁₀
                                                              && 1 <= i₁₀
                                                              && i₁₀ < i₂₄ + 1
                                                              && b₂₃[i₂₄ := b₂₃[i₂₄ - 1] + a₂₁[i₂₄ - 1]][x₁₁] == b[0 := 1][-1 + i₁₀] + a₂₁[-1 + i₁₀])))
                                              && (forall x₁₁: int ::
                                                      (exists i₁₀: int ::
                                                              x₁₁ == i₁₀
                                                              && 1 <= i₁₀
                                                              && i₁₀ < i₂₄ + 1)
                                                      || b₂₃[i₂₄ := b₂₃[i₂₄ - 1] + a₂₁[i₂₄ - 1]][x₁₁] == b[0 := 1][x₁₁])
                                              && (forall i₁₀: int ::
                                                    (  1 <= i₁₀
                                                      && i₁₀ < i₂₄ + 1
                                                       ==> i₁₀ < N₂₀)))
                                          &&   i₂₄ < N₂₀
                                            ||   1 <= 1
                                              && 1 <= N₂₀
                                              && (forall x₁₅: int, i₁₄: int ::
                                                    (  x₁₅ == i₁₄
                                                      && 1 <= i₁₄
                                                      && i₁₄ < 1
                                                       ==> (exists i₁₄: int ::
                                                              i₁₄ < N₂₀
                                                              && x₁₅ == i₁₄
                                                              && 1 <= i₁₄
                                                              && i₁₄ < 1
                                                              && c[0 := 0][x₁₅] == c[0 := 0][-1 + i₁₄] + b₂₃[-1 + i₁₄])))
                                              && (forall x₁₅: int ::
                                                      (exists i₁₄: int ::
                                                              x₁₅ == i₁₄
                                                              && 1 <= i₁₄
                                                              && i₁₄ < 1)
                                                      || c[0 := 0][x₁₅] == c[0 := 0][x₁₅])
                                              && (forall i₁₄: int ::
                                                    (  1 <= i₁₄
                                                      && i₁₄ < 1
                                                       ==> i₁₄ < N₂₀))
                                              && (forall c₂₅: [int]int, i₂₆: int ::
                                                    (  1 <= i₂₆
                                                      && i₂₆ <= N₂₀
                                                      && (forall x₁₅: int, i₁₄: int ::
                                                            (  x₁₅ == i₁₄
                                                              && 1 <= i₁₄
                                                              && i₁₄ < i₂₆
                                                               ==> (exists i₁₄: int ::
                                                                      i₁₄ < N₂₀
                                                                      && x₁₅ == i₁₄
                                                                      && 1 <= i₁₄
                                                                      && i₁₄ < i₂₆
                                                                      && c₂₅[x₁₅] == c[0 := 0][-1 + i₁₄] + b₂₃[-1 + i₁₄])))
                                                      && (forall x₁₅: int ::
                                                              (exists i₁₄: int ::
                                                                      x₁₅ == i₁₄
                                                                      && 1 <= i₁₄
                                                                      && i₁₄ < i₂₆)
                                                              || c₂₅[x₁₅] == c[0 := 0][x₁₅])
                                                      && (forall i₁₄: int ::
                                                            (  1 <= i₁₄
                                                              && i₁₄ < i₂₆
                                                               ==> i₁₄ < N₂₀))
                                                       ==> (i₂₆ < N₂₀
                                                           ==> 1 <= i₂₆ + 1
                                                            && i₂₆ + 1 <= N₂₀
                                                            && (forall x₁₅: int, i₁₄: int ::
                                                                  (  x₁₅ == i₁₄
                                                                    && 1 <= i₁₄
                                                                    && i₁₄ < i₂₆ + 1
                                                                     ==> (exists i₁₄: int ::
                                                                            i₁₄ < N₂₀
                                                                            && x₁₅ == i₁₄
                                                                            && 1 <= i₁₄
                                                                            && i₁₄ < i₂₆ + 1
                                                                            && c₂₅[i₂₆ := c₂₅[i₂₆ - 1] + b₂₃[i₂₆ - 1]][x₁₅] == c[0 := 0][-1 + i₁₄] + b₂₃[-1 + i₁₄])))
                                                            && (forall x₁₅: int ::
                                                                    (exists i₁₄: int ::
                                                                            x₁₅ == i₁₄
                                                                            && 1 <= i₁₄
                                                                            && i₁₄ < i₂₆ + 1)
                                                                    || c₂₅[i₂₆ := c₂₅[i₂₆ - 1] + b₂₃[i₂₆ - 1]][x₁₅] == c[0 := 0][x₁₅])
                                                            && (forall i₁₄: int ::
                                                                  (  1 <= i₁₄
                                                                    && i₁₄ < i₂₆ + 1
                                                                     ==> i₁₄ < N₂₀)))
                                                        &&   i₂₆ < N₂₀
                                                          ||   0 <= 0
                                                            && 0 <= N₂₀
                                                            && (forall i₁₈: int ::
                                                                  (  0 <= i₁₈
                                                                    && i₁₈ < 0
                                                                     ==> i₁₈ < N₂₀))
                                                            && (forall i₂₇: int ::
                                                                  (  0 <= i₂₇
                                                                    && i₂₇ <= N₂₀
                                                                    && (forall i₁₈: int ::
                                                                          (  0 <= i₁₈
                                                                            && i₁₈ < i₂₇
                                                                             ==> i₁₈ < N₂₀))
                                                                     ==> (i₂₇ < N₂₀
                                                                       ==> c₂₅[i₂₇] == i₂₇ * i₂₇ * i₂₇
                                                                        && 0 <= i₂₇ + 1
                                                                        && i₂₇ + 1 <= N₂₀
                                                                        && (forall i₁₈: int ::
                                                                              (  0 <= i₁₈
                                                                                && i₁₈ < i₂₇ + 1
                                                                                 ==> i₁₈ < N₂₀))))))))))))));


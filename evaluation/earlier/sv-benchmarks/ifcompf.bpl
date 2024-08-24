data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₀: int ::
        N₂₀ <= 0
        || (forall a: [int]int, b: [int]int, c: [int]int ::
              (N₂₀ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₂₀
                  && (forall x₇: int, i₆: int ::
                        (  x₇ == 0
                          && x₇ == i₆
                          && 0 <= i₆
                          && i₆ < 0
                           ==> (exists i₆: int ::
                                    i₆ == 0
                                    && i₆ < N₂₀
                                    && x₇ == 0
                                    && a[x₇] == 0)
                            || (exists i₆: int ::
                                  (i₆ == 0
                                     ==> false))))
                  && (forall x₇: int ::
                          (exists i₆: int ::
                                  x₇ == 0
                                  && x₇ == i₆
                                  && 0 <= i₆
                                  && i₆ < 0)
                          || a[x₇] == a[x₇])
                  && (forall i₆: int ::
                        (  0 <= i₆
                          && i₆ < 0
                           ==> i₆ < N₂₀))
                  && (forall a₂₁: [int]int, i₂₂: int ::
                        (  0 <= i₂₂
                          && i₂₂ <= N₂₀
                          && (forall x₇: int, i₆: int ::
                                (  x₇ == 0
                                  && x₇ == i₆
                                  && 0 <= i₆
                                  && i₆ < i₂₂
                                   ==> (exists i₆: int ::
                                            i₆ == 0
                                            && i₆ < N₂₀
                                            && x₇ == 0
                                            && a₂₁[x₇] == 0)
                                    || (exists i₆: int ::
                                          (i₆ == 0
                                             ==> false))))
                          && (forall x₇: int ::
                                  (exists i₆: int ::
                                          x₇ == 0
                                          && x₇ == i₆
                                          && 0 <= i₆
                                          && i₆ < i₂₂)
                                  || a₂₁[x₇] == a[x₇])
                          && (forall i₆: int ::
                                (  0 <= i₆
                                  && i₆ < i₂₂
                                   ==> i₆ < N₂₀))
                           ==> (i₂₂ < N₂₀
                               ==> (i₂₂ == 0
                                   ==> 0 <= i₂₂ + 1
                                    && i₂₂ + 1 <= N₂₀
                                    && (forall x₇: int, i₆: int ::
                                          (  x₇ == 0
                                            && x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₂₂ + 1
                                             ==> (exists i₆: int ::
                                                      i₆ == 0
                                                      && i₆ < N₂₀
                                                      && x₇ == 0
                                                      && a₂₁[0 := 0][x₇] == 0)
                                              || (exists i₆: int ::
                                                    (i₆ == 0
                                                       ==> false))))
                                    && (forall x₇: int ::
                                            (exists i₆: int ::
                                                    x₇ == 0
                                                    && x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₂₂ + 1)
                                            || a₂₁[0 := 0][x₇] == a[x₇])
                                    && (forall i₆: int ::
                                          (  0 <= i₆
                                            && i₆ < i₂₂ + 1
                                             ==> i₆ < N₂₀)))
                                &&   i₂₂ == 0
                                  ||   0 <= i₂₂ + 1
                                    && i₂₂ + 1 <= N₂₀
                                    && (forall x₇: int, i₆: int ::
                                          (  x₇ == 0
                                            && x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₂₂ + 1
                                             ==> (exists i₆: int ::
                                                      i₆ == 0
                                                      && i₆ < N₂₀
                                                      && x₇ == 0
                                                      && a₂₁[i₂₂ := a₂₁[i₂₂ - 1] + 6][x₇] == 0)
                                              || (exists i₆: int ::
                                                    (i₆ == 0
                                                       ==> false))))
                                    && (forall x₇: int ::
                                            (exists i₆: int ::
                                                    x₇ == 0
                                                    && x₇ == i₆
                                                    && 0 <= i₆
                                                    && i₆ < i₂₂ + 1)
                                            || a₂₁[i₂₂ := a₂₁[i₂₂ - 1] + 6][x₇] == a[x₇])
                                    && (forall i₆: int ::
                                          (  0 <= i₆
                                            && i₆ < i₂₂ + 1
                                             ==> i₆ < N₂₀)))
                            &&   i₂₂ < N₂₀
                              ||   0 <= 0
                                && 0 <= N₂₀
                                && (forall x₁₁: int, i₁₀: int ::
                                      (  x₁₁ == 0
                                        && x₁₁ == i₁₀
                                        && 0 <= i₁₀
                                        && i₁₀ < 0
                                         ==> (exists i₁₀: int ::
                                                  i₁₀ == 0
                                                  && i₁₀ < N₂₀
                                                  && x₁₁ == 0
                                                  && b[x₁₁] == 1)
                                          || (exists i₁₀: int ::
                                                (i₁₀ == 0
                                                   ==> false))))
                                && (forall x₁₁: int ::
                                        (exists i₁₀: int ::
                                                x₁₁ == 0
                                                && x₁₁ == i₁₀
                                                && 0 <= i₁₀
                                                && i₁₀ < 0)
                                        || b[x₁₁] == b[x₁₁])
                                && (forall i₁₀: int ::
                                      (  0 <= i₁₀
                                        && i₁₀ < 0
                                         ==> i₁₀ < N₂₀))
                                && (forall b₂₃: [int]int, i₂₄: int ::
                                      (  0 <= i₂₄
                                        && i₂₄ <= N₂₀
                                        && (forall x₁₁: int, i₁₀: int ::
                                              (  x₁₁ == 0
                                                && x₁₁ == i₁₀
                                                && 0 <= i₁₀
                                                && i₁₀ < i₂₄
                                                 ==> (exists i₁₀: int ::
                                                          i₁₀ == 0
                                                          && i₁₀ < N₂₀
                                                          && x₁₁ == 0
                                                          && b₂₃[x₁₁] == 1)
                                                  || (exists i₁₀: int ::
                                                        (i₁₀ == 0
                                                           ==> false))))
                                        && (forall x₁₁: int ::
                                                (exists i₁₀: int ::
                                                        x₁₁ == 0
                                                        && x₁₁ == i₁₀
                                                        && 0 <= i₁₀
                                                        && i₁₀ < i₂₄)
                                                || b₂₃[x₁₁] == b[x₁₁])
                                        && (forall i₁₀: int ::
                                              (  0 <= i₁₀
                                                && i₁₀ < i₂₄
                                                 ==> i₁₀ < N₂₀))
                                         ==> (i₂₄ < N₂₀
                                             ==> (i₂₄ == 0
                                                 ==> 0 <= i₂₄ + 1
                                                  && i₂₄ + 1 <= N₂₀
                                                  && (forall x₁₁: int, i₁₀: int ::
                                                        (  x₁₁ == 0
                                                          && x₁₁ == i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < i₂₄ + 1
                                                           ==> (exists i₁₀: int ::
                                                                    i₁₀ == 0
                                                                    && i₁₀ < N₂₀
                                                                    && x₁₁ == 0
                                                                    && b₂₃[0 := 1][x₁₁] == 1)
                                                            || (exists i₁₀: int ::
                                                                  (i₁₀ == 0
                                                                     ==> false))))
                                                  && (forall x₁₁: int ::
                                                          (exists i₁₀: int ::
                                                                  x₁₁ == 0
                                                                  && x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₂₄ + 1)
                                                          || b₂₃[0 := 1][x₁₁] == b[x₁₁])
                                                  && (forall i₁₀: int ::
                                                        (  0 <= i₁₀
                                                          && i₁₀ < i₂₄ + 1
                                                           ==> i₁₀ < N₂₀)))
                                              &&   i₂₄ == 0
                                                ||   0 <= i₂₄ + 1
                                                  && i₂₄ + 1 <= N₂₀
                                                  && (forall x₁₁: int, i₁₀: int ::
                                                        (  x₁₁ == 0
                                                          && x₁₁ == i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < i₂₄ + 1
                                                           ==> (exists i₁₀: int ::
                                                                    i₁₀ == 0
                                                                    && i₁₀ < N₂₀
                                                                    && x₁₁ == 0
                                                                    && b₂₃[i₂₄ := b₂₃[i₂₄ - 1] + a₂₁[i₂₄ - 1]][x₁₁] == 1)
                                                            || (exists i₁₀: int ::
                                                                  (i₁₀ == 0
                                                                     ==> false))))
                                                  && (forall x₁₁: int ::
                                                          (exists i₁₀: int ::
                                                                  x₁₁ == 0
                                                                  && x₁₁ == i₁₀
                                                                  && 0 <= i₁₀
                                                                  && i₁₀ < i₂₄ + 1)
                                                          || b₂₃[i₂₄ := b₂₃[i₂₄ - 1] + a₂₁[i₂₄ - 1]][x₁₁] == b[x₁₁])
                                                  && (forall i₁₀: int ::
                                                        (  0 <= i₁₀
                                                          && i₁₀ < i₂₄ + 1
                                                           ==> i₁₀ < N₂₀)))
                                          &&   i₂₄ < N₂₀
                                            ||   0 <= 0
                                              && 0 <= N₂₀
                                              && (forall x₁₅: int, i₁₄: int ::
                                                    (  x₁₅ == 0
                                                      && x₁₅ == i₁₄
                                                      && 0 <= i₁₄
                                                      && i₁₄ < 0
                                                       ==> (exists i₁₄: int ::
                                                                i₁₄ == 0
                                                                && i₁₄ < N₂₀
                                                                && x₁₅ == 0
                                                                && c[x₁₅] == 0)
                                                        || (exists i₁₄: int ::
                                                              (i₁₄ == 0
                                                                 ==> false))))
                                              && (forall x₁₅: int ::
                                                      (exists i₁₄: int ::
                                                              x₁₅ == 0
                                                              && x₁₅ == i₁₄
                                                              && 0 <= i₁₄
                                                              && i₁₄ < 0)
                                                      || c[x₁₅] == c[x₁₅])
                                              && (forall i₁₄: int ::
                                                    (  0 <= i₁₄
                                                      && i₁₄ < 0
                                                       ==> i₁₄ < N₂₀))
                                              && (forall c₂₅: [int]int, i₂₆: int ::
                                                    (  0 <= i₂₆
                                                      && i₂₆ <= N₂₀
                                                      && (forall x₁₅: int, i₁₄: int ::
                                                            (  x₁₅ == 0
                                                              && x₁₅ == i₁₄
                                                              && 0 <= i₁₄
                                                              && i₁₄ < i₂₆
                                                               ==> (exists i₁₄: int ::
                                                                        i₁₄ == 0
                                                                        && i₁₄ < N₂₀
                                                                        && x₁₅ == 0
                                                                        && c₂₅[x₁₅] == 0)
                                                                || (exists i₁₄: int ::
                                                                      (i₁₄ == 0
                                                                         ==> false))))
                                                      && (forall x₁₅: int ::
                                                              (exists i₁₄: int ::
                                                                      x₁₅ == 0
                                                                      && x₁₅ == i₁₄
                                                                      && 0 <= i₁₄
                                                                      && i₁₄ < i₂₆)
                                                              || c₂₅[x₁₅] == c[x₁₅])
                                                      && (forall i₁₄: int ::
                                                            (  0 <= i₁₄
                                                              && i₁₄ < i₂₆
                                                               ==> i₁₄ < N₂₀))
                                                       ==> (i₂₆ < N₂₀
                                                           ==> (i₂₆ == 0
                                                               ==> 0 <= i₂₆ + 1
                                                                && i₂₆ + 1 <= N₂₀
                                                                && (forall x₁₅: int, i₁₄: int ::
                                                                      (  x₁₅ == 0
                                                                        && x₁₅ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₂₆ + 1
                                                                         ==> (exists i₁₄: int ::
                                                                                  i₁₄ == 0
                                                                                  && i₁₄ < N₂₀
                                                                                  && x₁₅ == 0
                                                                                  && c₂₅[0 := 0][x₁₅] == 0)
                                                                          || (exists i₁₄: int ::
                                                                                (i₁₄ == 0
                                                                                   ==> false))))
                                                                && (forall x₁₅: int ::
                                                                        (exists i₁₄: int ::
                                                                                x₁₅ == 0
                                                                                && x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₂₆ + 1)
                                                                        || c₂₅[0 := 0][x₁₅] == c[x₁₅])
                                                                && (forall i₁₄: int ::
                                                                      (  0 <= i₁₄
                                                                        && i₁₄ < i₂₆ + 1
                                                                         ==> i₁₄ < N₂₀)))
                                                            &&   i₂₆ == 0
                                                              ||   0 <= i₂₆ + 1
                                                                && i₂₆ + 1 <= N₂₀
                                                                && (forall x₁₅: int, i₁₄: int ::
                                                                      (  x₁₅ == 0
                                                                        && x₁₅ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₂₆ + 1
                                                                         ==> (exists i₁₄: int ::
                                                                                  i₁₄ == 0
                                                                                  && i₁₄ < N₂₀
                                                                                  && x₁₅ == 0
                                                                                  && c₂₅[i₂₆ := c₂₅[i₂₆ - 1] + b₂₃[i₂₆ - 1]][x₁₅] == 0)
                                                                          || (exists i₁₄: int ::
                                                                                (i₁₄ == 0
                                                                                   ==> false))))
                                                                && (forall x₁₅: int ::
                                                                        (exists i₁₄: int ::
                                                                                x₁₅ == 0
                                                                                && x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₂₆ + 1)
                                                                        || c₂₅[i₂₆ := c₂₅[i₂₆ - 1] + b₂₃[i₂₆ - 1]][x₁₅] == c[x₁₅])
                                                                && (forall i₁₄: int ::
                                                                      (  0 <= i₁₄
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


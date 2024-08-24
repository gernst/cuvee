data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₂: int ::
        N₂₂ <= 0
        || (forall a: [int]int ::
              (N₂₂ <= 2147483647 / 4
                 ==> 0 <= 0
                  && 0 <= N₂₂
                  && (forall x₅: int, i₄: int ::
                        (  x₅ == i₄
                          && 0 <= i₄
                          && i₄ < 0
                           ==> (exists i₄: int ::
                                  i₄ < N₂₂
                                  && x₅ == i₄
                                  && 0 <= i₄
                                  && i₄ < 0
                                  && a[x₅] == 1 + i₄ * i₄ + -2 * i₄)))
                  && (forall x₅: int ::
                          (exists i₄: int ::
                                  x₅ == i₄
                                  && 0 <= i₄
                                  && i₄ < 0)
                          || a[x₅] == a[x₅])
                  && (forall i₄: int ::
                        (  0 <= i₄
                          && i₄ < 0
                           ==> i₄ < N₂₂))
                  && (forall a₂₃: [int]int, i₂₄: int ::
                        (  0 <= i₂₄
                          && i₂₄ <= N₂₂
                          && (forall x₅: int, i₄: int ::
                                (  x₅ == i₄
                                  && 0 <= i₄
                                  && i₄ < i₂₄
                                   ==> (exists i₄: int ::
                                          i₄ < N₂₂
                                          && x₅ == i₄
                                          && 0 <= i₄
                                          && i₄ < i₂₄
                                          && a₂₃[x₅] == 1 + i₄ * i₄ + -2 * i₄)))
                          && (forall x₅: int ::
                                  (exists i₄: int ::
                                          x₅ == i₄
                                          && 0 <= i₄
                                          && i₄ < i₂₄)
                                  || a₂₃[x₅] == a[x₅])
                          && (forall i₄: int ::
                                (  0 <= i₄
                                  && i₄ < i₂₄
                                   ==> i₄ < N₂₂))
                           ==> (i₂₄ < N₂₂
                               ==> 0 <= i₂₄ + 1
                                && i₂₄ + 1 <= N₂₂
                                && (forall x₅: int, i₄: int ::
                                      (  x₅ == i₄
                                        && 0 <= i₄
                                        && i₄ < i₂₄ + 1
                                         ==> (exists i₄: int ::
                                                i₄ < N₂₂
                                                && x₅ == i₄
                                                && 0 <= i₄
                                                && i₄ < i₂₄ + 1
                                                && a₂₃[i₂₄ := (i₂₄ - 1) * (i₂₄ - 1)][x₅] == 1 + i₄ * i₄ + -2 * i₄)))
                                && (forall x₅: int ::
                                        (exists i₄: int ::
                                                x₅ == i₄
                                                && 0 <= i₄
                                                && i₄ < i₂₄ + 1)
                                        || a₂₃[i₂₄ := (i₂₄ - 1) * (i₂₄ - 1)][x₅] == a[x₅])
                                && (forall i₄: int ::
                                      (  0 <= i₄
                                        && i₄ < i₂₄ + 1
                                         ==> i₄ < N₂₂)))
                            &&   i₂₄ < N₂₂
                              ||   0 <= 0
                                && 0 <= N₂₂
                                && (forall x₉: int, i₈: int ::
                                      (  x₉ == i₈
                                        && 0 <= i₈
                                        && i₈ < 0
                                         ==> (exists i₈: int ::
                                                i₈ < N₂₂
                                                && x₉ == i₈
                                                && 0 <= i₈
                                                && i₈ < 0
                                                && a₂₃[x₉] == i₈ + a₂₃[i₈])))
                                && (forall x₉: int ::
                                        (exists i₈: int ::
                                                x₉ == i₈
                                                && 0 <= i₈
                                                && i₈ < 0)
                                        || a₂₃[x₉] == a₂₃[x₉])
                                && (forall i₈: int ::
                                      (  0 <= i₈
                                        && i₈ < 0
                                         ==> i₈ < N₂₂))
                                && (forall a₂₅: [int]int, i₂₆: int ::
                                      (  0 <= i₂₆
                                        && i₂₆ <= N₂₂
                                        && (forall x₉: int, i₈: int ::
                                              (  x₉ == i₈
                                                && 0 <= i₈
                                                && i₈ < i₂₆
                                                 ==> (exists i₈: int ::
                                                        i₈ < N₂₂
                                                        && x₉ == i₈
                                                        && 0 <= i₈
                                                        && i₈ < i₂₆
                                                        && a₂₅[x₉] == i₈ + a₂₃[i₈])))
                                        && (forall x₉: int ::
                                                (exists i₈: int ::
                                                        x₉ == i₈
                                                        && 0 <= i₈
                                                        && i₈ < i₂₆)
                                                || a₂₅[x₉] == a₂₃[x₉])
                                        && (forall i₈: int ::
                                              (  0 <= i₈
                                                && i₈ < i₂₆
                                                 ==> i₈ < N₂₂))
                                         ==> (i₂₆ < N₂₂
                                             ==> 0 <= i₂₆ + 1
                                              && i₂₆ + 1 <= N₂₂
                                              && (forall x₉: int, i₈: int ::
                                                    (  x₉ == i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₂₆ + 1
                                                       ==> (exists i₈: int ::
                                                              i₈ < N₂₂
                                                              && x₉ == i₈
                                                              && 0 <= i₈
                                                              && i₈ < i₂₆ + 1
                                                              && a₂₅[i₂₆ := a₂₅[i₂₆] + i₂₆][x₉] == i₈ + a₂₃[i₈])))
                                              && (forall x₉: int ::
                                                      (exists i₈: int ::
                                                              x₉ == i₈
                                                              && 0 <= i₈
                                                              && i₈ < i₂₆ + 1)
                                                      || a₂₅[i₂₆ := a₂₅[i₂₆] + i₂₆][x₉] == a₂₃[x₉])
                                              && (forall i₈: int ::
                                                    (  0 <= i₈
                                                      && i₈ < i₂₆ + 1
                                                       ==> i₈ < N₂₂)))
                                          &&   i₂₆ < N₂₂
                                            ||   0 <= 0
                                              && 0 <= N₂₂
                                              && (forall x₁₃: int, i₁₂: int ::
                                                    (  x₁₃ == i₁₂
                                                      && 0 <= i₁₂
                                                      && i₁₂ < 0
                                                       ==> (exists i₁₂: int ::
                                                              i₁₂ < N₂₂
                                                              && x₁₃ == i₁₂
                                                              && 0 <= i₁₂
                                                              && i₁₂ < 0
                                                              && a₂₅[x₁₃] == a₂₅[i₁₂] + i₁₂)))
                                              && (forall x₁₃: int ::
                                                      (exists i₁₂: int ::
                                                              x₁₃ == i₁₂
                                                              && 0 <= i₁₂
                                                              && i₁₂ < 0)
                                                      || a₂₅[x₁₃] == a₂₅[x₁₃])
                                              && (forall i₁₂: int ::
                                                    (  0 <= i₁₂
                                                      && i₁₂ < 0
                                                       ==> i₁₂ < N₂₂))
                                              && (forall a₂₇: [int]int, i₂₈: int ::
                                                    (  0 <= i₂₈
                                                      && i₂₈ <= N₂₂
                                                      && (forall x₁₃: int, i₁₂: int ::
                                                            (  x₁₃ == i₁₂
                                                              && 0 <= i₁₂
                                                              && i₁₂ < i₂₈
                                                               ==> (exists i₁₂: int ::
                                                                      i₁₂ < N₂₂
                                                                      && x₁₃ == i₁₂
                                                                      && 0 <= i₁₂
                                                                      && i₁₂ < i₂₈
                                                                      && a₂₇[x₁₃] == a₂₅[i₁₂] + i₁₂)))
                                                      && (forall x₁₃: int ::
                                                              (exists i₁₂: int ::
                                                                      x₁₃ == i₁₂
                                                                      && 0 <= i₁₂
                                                                      && i₁₂ < i₂₈)
                                                              || a₂₇[x₁₃] == a₂₅[x₁₃])
                                                      && (forall i₁₂: int ::
                                                            (  0 <= i₁₂
                                                              && i₁₂ < i₂₈
                                                               ==> i₁₂ < N₂₂))
                                                       ==> (i₂₈ < N₂₂
                                                           ==> 0 <= i₂₈ + 1
                                                            && i₂₈ + 1 <= N₂₂
                                                            && (forall x₁₃: int, i₁₂: int ::
                                                                  (  x₁₃ == i₁₂
                                                                    && 0 <= i₁₂
                                                                    && i₁₂ < i₂₈ + 1
                                                                     ==> (exists i₁₂: int ::
                                                                            i₁₂ < N₂₂
                                                                            && x₁₃ == i₁₂
                                                                            && 0 <= i₁₂
                                                                            && i₁₂ < i₂₈ + 1
                                                                            && a₂₇[i₂₈ := a₂₇[i₂₈] + i₂₈][x₁₃] == a₂₅[i₁₂] + i₁₂)))
                                                            && (forall x₁₃: int ::
                                                                    (exists i₁₂: int ::
                                                                            x₁₃ == i₁₂
                                                                            && 0 <= i₁₂
                                                                            && i₁₂ < i₂₈ + 1)
                                                                    || a₂₇[i₂₈ := a₂₇[i₂₈] + i₂₈][x₁₃] == a₂₅[x₁₃])
                                                            && (forall i₁₂: int ::
                                                                  (  0 <= i₁₂
                                                                    && i₁₂ < i₂₈ + 1
                                                                     ==> i₁₂ < N₂₂)))
                                                        &&   i₂₈ < N₂₂
                                                          ||   0 <= 0
                                                            && 0 <= N₂₂
                                                            && (forall x₁₇: int, i₁₆: int ::
                                                                  (  x₁₇ == i₁₆
                                                                    && 0 <= i₁₆
                                                                    && i₁₆ < 0
                                                                     ==> (exists i₁₆: int ::
                                                                            i₁₆ < N₂₂
                                                                            && x₁₇ == i₁₆
                                                                            && 0 <= i₁₆
                                                                            && i₁₆ < 0
                                                                            && a₂₇[x₁₇] == -1 + a₂₇[i₁₆])))
                                                            && (forall x₁₇: int ::
                                                                    (exists i₁₆: int ::
                                                                            x₁₇ == i₁₆
                                                                            && 0 <= i₁₆
                                                                            && i₁₆ < 0)
                                                                    || a₂₇[x₁₇] == a₂₇[x₁₇])
                                                            && (forall i₁₆: int ::
                                                                  (  0 <= i₁₆
                                                                    && i₁₆ < 0
                                                                     ==> i₁₆ < N₂₂))
                                                            && (forall a₂₉: [int]int, i₃₀: int ::
                                                                  (  0 <= i₃₀
                                                                    && i₃₀ <= N₂₂
                                                                    && (forall x₁₇: int, i₁₆: int ::
                                                                          (  x₁₇ == i₁₆
                                                                            && 0 <= i₁₆
                                                                            && i₁₆ < i₃₀
                                                                             ==> (exists i₁₆: int ::
                                                                                    i₁₆ < N₂₂
                                                                                    && x₁₇ == i₁₆
                                                                                    && 0 <= i₁₆
                                                                                    && i₁₆ < i₃₀
                                                                                    && a₂₉[x₁₇] == -1 + a₂₇[i₁₆])))
                                                                    && (forall x₁₇: int ::
                                                                            (exists i₁₆: int ::
                                                                                    x₁₇ == i₁₆
                                                                                    && 0 <= i₁₆
                                                                                    && i₁₆ < i₃₀)
                                                                            || a₂₉[x₁₇] == a₂₇[x₁₇])
                                                                    && (forall i₁₆: int ::
                                                                          (  0 <= i₁₆
                                                                            && i₁₆ < i₃₀
                                                                             ==> i₁₆ < N₂₂))
                                                                     ==> (i₃₀ < N₂₂
                                                                         ==> 0 <= i₃₀ + 1
                                                                          && i₃₀ + 1 <= N₂₂
                                                                          && (forall x₁₇: int, i₁₆: int ::
                                                                                (  x₁₇ == i₁₆
                                                                                  && 0 <= i₁₆
                                                                                  && i₁₆ < i₃₀ + 1
                                                                                   ==> (exists i₁₆: int ::
                                                                                          i₁₆ < N₂₂
                                                                                          && x₁₇ == i₁₆
                                                                                          && 0 <= i₁₆
                                                                                          && i₁₆ < i₃₀ + 1
                                                                                          && a₂₉[i₃₀ := a₂₉[i₃₀] - 1][x₁₇] == -1 + a₂₇[i₁₆])))
                                                                          && (forall x₁₇: int ::
                                                                                  (exists i₁₆: int ::
                                                                                          x₁₇ == i₁₆
                                                                                          && 0 <= i₁₆
                                                                                          && i₁₆ < i₃₀ + 1)
                                                                                  || a₂₉[i₃₀ := a₂₉[i₃₀] - 1][x₁₇] == a₂₇[x₁₇])
                                                                          && (forall i₁₆: int ::
                                                                                (  0 <= i₁₆
                                                                                  && i₁₆ < i₃₀ + 1
                                                                                   ==> i₁₆ < N₂₂)))
                                                                      &&   i₃₀ < N₂₂
                                                                        ||   0 <= 0
                                                                          && 0 <= N₂₂
                                                                          && (forall i₂₀: int ::
                                                                                (  0 <= i₂₀
                                                                                  && i₂₀ < 0
                                                                                   ==> i₂₀ < N₂₂))
                                                                          && (forall i₃₁: int ::
                                                                                (  0 <= i₃₁
                                                                                  && i₃₁ <= N₂₂
                                                                                  && (forall i₂₀: int ::
                                                                                        (  0 <= i₂₀
                                                                                          && i₂₀ < i₃₁
                                                                                           ==> i₂₀ < N₂₂))
                                                                                   ==> (i₃₁ < N₂₂
                                                                                     ==> a₂₉[i₃₁] == i₃₁ * i₃₁ + 1
                                                                                      && 0 <= i₃₁ + 1
                                                                                      && i₃₁ + 1 <= N₂₂
                                                                                      && (forall i₂₀: int ::
                                                                                            (  0 <= i₂₀
                                                                                              && i₂₀ < i₃₁ + 1
                                                                                               ==> i₂₀ < N₂₂))))))))))))))));


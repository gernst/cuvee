data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> (forall N: int ::
        (forall a: [int]int ::
              (forall b: [int]int ::
                    (forall c: [int]int ::
                            true
                            && (0 < N
                               ==> true
                                && 1 <= 1
                                && 1 <= N
                                && (forall x₁₂: int ::
                                      ((exists i₁₁: int ::
                                              x₁₂ == i₁₁
                                              && 1 <= i₁₁
                                              && i₁₁ < 1)
                                         ==> (exists j₉: int, k₁₀: int, i₁₁: int ::
                                                j₉ + k₁₀ == 0
                                                && -10000 < k₁₀
                                                && k₁₀ < 10000
                                                && -10000 < j₉
                                                && j₉ < 10000
                                                && i₁₁ < N
                                                && x₁₂ == i₁₁
                                                && 1 <= i₁₁
                                                && i₁₁ < 1
                                                && a[x₁₂] == j₉)))
                                && (forall x₁₂: int ::
                                      (!((exists i₁₁: int ::
                                              x₁₂ == i₁₁
                                              && 1 <= i₁₁
                                              && i₁₁ < 1)
                                      )
                                         ==> a[x₁₂] == a[x₁₂]))
                                && (forall x₁₃: int ::
                                      ((exists i₁₁: int ::
                                              x₁₃ == i₁₁
                                              && 1 <= i₁₁
                                              && i₁₁ < 1)
                                         ==> (exists j₉: int, k₁₀: int, i₁₁: int ::
                                                j₉ + k₁₀ == 0
                                                && -10000 < k₁₀
                                                && k₁₀ < 10000
                                                && -10000 < j₉
                                                && j₉ < 10000
                                                && i₁₁ < N
                                                && x₁₃ == i₁₁
                                                && 1 <= i₁₁
                                                && i₁₁ < 1
                                                && b[x₁₃] == -k₁₀)))
                                && (forall x₁₃: int ::
                                      (!((exists i₁₁: int ::
                                              x₁₃ == i₁₁
                                              && 1 <= i₁₁
                                              && i₁₁ < 1)
                                      )
                                         ==> b[x₁₃] == b[x₁₃]))
                                && (forall i₁₁: int ::
                                      (  1 <= i₁₁
                                        && i₁₁ < 1
                                         ==> i₁₁ < N))
                                && (forall a₂₃: [int]int, b₂₄: [int]int, i₂₅: int ::
                                      (  true
                                        && 1 <= i₂₅
                                        && i₂₅ <= N
                                        && (forall x₁₂: int ::
                                              ((exists i₁₁: int ::
                                                      x₁₂ == i₁₁
                                                      && 1 <= i₁₁
                                                      && i₁₁ < i₂₅)
                                                 ==> (exists j₉: int, k₁₀: int, i₁₁: int ::
                                                        j₉ + k₁₀ == 0
                                                        && -10000 < k₁₀
                                                        && k₁₀ < 10000
                                                        && -10000 < j₉
                                                        && j₉ < 10000
                                                        && i₁₁ < N
                                                        && x₁₂ == i₁₁
                                                        && 1 <= i₁₁
                                                        && i₁₁ < i₂₅
                                                        && a₂₃[x₁₂] == j₉)))
                                        && (forall x₁₂: int ::
                                              (!((exists i₁₁: int ::
                                                      x₁₂ == i₁₁
                                                      && 1 <= i₁₁
                                                      && i₁₁ < i₂₅)
                                              )
                                                 ==> a₂₃[x₁₂] == a[x₁₂]))
                                        && (forall x₁₃: int ::
                                              ((exists i₁₁: int ::
                                                      x₁₃ == i₁₁
                                                      && 1 <= i₁₁
                                                      && i₁₁ < i₂₅)
                                                 ==> (exists j₉: int, k₁₀: int, i₁₁: int ::
                                                        j₉ + k₁₀ == 0
                                                        && -10000 < k₁₀
                                                        && k₁₀ < 10000
                                                        && -10000 < j₉
                                                        && j₉ < 10000
                                                        && i₁₁ < N
                                                        && x₁₃ == i₁₁
                                                        && 1 <= i₁₁
                                                        && i₁₁ < i₂₅
                                                        && b₂₄[x₁₃] == -k₁₀)))
                                        && (forall x₁₃: int ::
                                              (!((exists i₁₁: int ::
                                                      x₁₃ == i₁₁
                                                      && 1 <= i₁₁
                                                      && i₁₁ < i₂₅)
                                              )
                                                 ==> b₂₄[x₁₃] == b[x₁₃]))
                                        && (forall i₁₁: int ::
                                              (  1 <= i₁₁
                                                && i₁₁ < i₂₅
                                                 ==> i₁₁ < N))
                                         ==> (i₂₅ < N
                                             ==> (forall j: int ::
                                                  (forall k: int ::
                                                          true
                                                          && (  -10000 < j
                                                            && j < 10000
                                                             ==> true
                                                              && (  -10000 < k
                                                                && k < 10000
                                                                 ==> true
                                                                  && (j + k == 0
                                                                     ==> true
                                                                      && 1 <= i₂₅ + 1
                                                                      && i₂₅ + 1 <= N
                                                                      && (forall x₁₂: int ::
                                                                            ((exists i₁₁: int ::
                                                                                    x₁₂ == i₁₁
                                                                                    && 1 <= i₁₁
                                                                                    && i₁₁ < i₂₅ + 1)
                                                                               ==> (exists j₉: int, k₁₀: int, i₁₁: int ::
                                                                                      j₉ + k₁₀ == 0
                                                                                      && -10000 < k₁₀
                                                                                      && k₁₀ < 10000
                                                                                      && -10000 < j₉
                                                                                      && j₉ < 10000
                                                                                      && i₁₁ < N
                                                                                      && x₁₂ == i₁₁
                                                                                      && 1 <= i₁₁
                                                                                      && i₁₁ < i₂₅ + 1
                                                                                      && a₂₃[i₂₅ := j][x₁₂] == j₉)))
                                                                      && (forall x₁₂: int ::
                                                                            (!((exists i₁₁: int ::
                                                                                    x₁₂ == i₁₁
                                                                                    && 1 <= i₁₁
                                                                                    && i₁₁ < i₂₅ + 1)
                                                                            )
                                                                               ==> a₂₃[i₂₅ := j][x₁₂] == a[x₁₂]))
                                                                      && (forall x₁₃: int ::
                                                                            ((exists i₁₁: int ::
                                                                                    x₁₃ == i₁₁
                                                                                    && 1 <= i₁₁
                                                                                    && i₁₁ < i₂₅ + 1)
                                                                               ==> (exists j₉: int, k₁₀: int, i₁₁: int ::
                                                                                      j₉ + k₁₀ == 0
                                                                                      && -10000 < k₁₀
                                                                                      && k₁₀ < 10000
                                                                                      && -10000 < j₉
                                                                                      && j₉ < 10000
                                                                                      && i₁₁ < N
                                                                                      && x₁₃ == i₁₁
                                                                                      && 1 <= i₁₁
                                                                                      && i₁₁ < i₂₅ + 1
                                                                                      && b₂₄[i₂₅ := -k][x₁₃] == -k₁₀)))
                                                                      && (forall x₁₃: int ::
                                                                            (!((exists i₁₁: int ::
                                                                                    x₁₃ == i₁₁
                                                                                    && 1 <= i₁₁
                                                                                    && i₁₁ < i₂₅ + 1)
                                                                            )
                                                                               ==> b₂₄[i₂₅ := -k][x₁₃] == b[x₁₃]))
                                                                      && (forall i₁₁: int ::
                                                                            (  1 <= i₁₁
                                                                              && i₁₁ < i₂₅ + 1
                                                                               ==> i₁₁ < N))
                                                                      && true
                                                                      && (true
                                                                         ==> true)))))))
                                          && (!(i₂₅ < N
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= N
                                                  && (forall x₁₈: int ::
                                                        ((exists i₁₇: int ::
                                                                x₁₈ == i₁₇
                                                                && 0 <= i₁₇
                                                                && i₁₇ < 0)
                                                           ==> (exists i₁₇: int ::
                                                                  i₁₇ < N
                                                                  && x₁₈ == i₁₇
                                                                  && 0 <= i₁₇
                                                                  && i₁₇ < 0
                                                                  && c[x₁₈] == a₂₃[i₁₇] + b₂₄[i₁₇])))
                                                  && (forall x₁₈: int ::
                                                        (!((exists i₁₇: int ::
                                                                x₁₈ == i₁₇
                                                                && 0 <= i₁₇
                                                                && i₁₇ < 0)
                                                        )
                                                           ==> c[x₁₈] == c[x₁₈]))
                                                  && (forall i₁₇: int ::
                                                        (  0 <= i₁₇
                                                          && i₁₇ < 0
                                                           ==> i₁₇ < N))
                                                  && (forall c₂₆: [int]int, i₂₇: int ::
                                                        (  true
                                                          && 0 <= i₂₇
                                                          && i₂₇ <= N
                                                          && (forall x₁₈: int ::
                                                                ((exists i₁₇: int ::
                                                                        x₁₈ == i₁₇
                                                                        && 0 <= i₁₇
                                                                        && i₁₇ < i₂₇)
                                                                   ==> (exists i₁₇: int ::
                                                                          i₁₇ < N
                                                                          && x₁₈ == i₁₇
                                                                          && 0 <= i₁₇
                                                                          && i₁₇ < i₂₇
                                                                          && c₂₆[x₁₈] == a₂₃[i₁₇] + b₂₄[i₁₇])))
                                                          && (forall x₁₈: int ::
                                                                (!((exists i₁₇: int ::
                                                                        x₁₈ == i₁₇
                                                                        && 0 <= i₁₇
                                                                        && i₁₇ < i₂₇)
                                                                )
                                                                   ==> c₂₆[x₁₈] == c[x₁₈]))
                                                          && (forall i₁₇: int ::
                                                                (  0 <= i₁₇
                                                                  && i₁₇ < i₂₇
                                                                   ==> i₁₇ < N))
                                                           ==> (i₂₇ < N
                                                               ==> true
                                                                && 0 <= i₂₇ + 1
                                                                && i₂₇ + 1 <= N
                                                                && (forall x₁₈: int ::
                                                                      ((exists i₁₇: int ::
                                                                              x₁₈ == i₁₇
                                                                              && 0 <= i₁₇
                                                                              && i₁₇ < i₂₇ + 1)
                                                                         ==> (exists i₁₇: int ::
                                                                                i₁₇ < N
                                                                                && x₁₈ == i₁₇
                                                                                && 0 <= i₁₇
                                                                                && i₁₇ < i₂₇ + 1
                                                                                && c₂₆[i₂₇ := a₂₃[i₂₇] + b₂₄[i₂₇]][x₁₈] == a₂₃[i₁₇] + b₂₄[i₁₇])))
                                                                && (forall x₁₈: int ::
                                                                      (!((exists i₁₇: int ::
                                                                              x₁₈ == i₁₇
                                                                              && 0 <= i₁₇
                                                                              && i₁₇ < i₂₇ + 1)
                                                                      )
                                                                         ==> c₂₆[i₂₇ := a₂₃[i₂₇] + b₂₄[i₂₇]][x₁₈] == c[x₁₈]))
                                                                && (forall i₁₇: int ::
                                                                      (  0 <= i₁₇
                                                                        && i₁₇ < i₂₇ + 1
                                                                         ==> i₁₇ < N))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (!(i₂₇ < N
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true
                                                                    && 1 <= 1
                                                                    && 1 <= N
                                                                    && (forall i₂₁: int ::
                                                                          (  1 <= i₂₁
                                                                            && i₂₁ < 1
                                                                             ==> i₂₁ < N))
                                                                    && (forall i₂₈: int ::
                                                                          (  true
                                                                            && 1 <= i₂₈
                                                                            && i₂₈ <= N
                                                                            && (forall i₂₁: int ::
                                                                                  (  1 <= i₂₁
                                                                                    && i₂₁ < i₂₈
                                                                                     ==> i₂₁ < N))
                                                                             ==> (i₂₈ < N
                                                                                 ==> c₂₆[i₂₈] == 0
                                                                                  && (true
                                                                                     ==> true
                                                                                      && 1 <= i₂₈ + 1
                                                                                      && i₂₈ + 1 <= N
                                                                                      && (forall i₂₁: int ::
                                                                                            (  1 <= i₂₁
                                                                                              && i₂₁ < i₂₈ + 1
                                                                                               ==> i₂₁ < N))
                                                                                      && true
                                                                                      && (true
                                                                                         ==> true)))
                                                                              && (!(i₂₈ < N
                                                                              )
                                                                                 ==> true
                                                                                  && (true
                                                                                     ==> true))))))))))))))))));


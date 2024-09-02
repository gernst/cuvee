data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> (forall N: int ::
        (forall a: [int]int ::
              (forall b: [int]int ::
                      true
                      && (0 < N
                         ==> true
                          && 1 <= 1
                          && 1 <= N
                          && (forall x₁₁: int ::
                                ((exists i₁₀: int ::
                                        x₁₁ == i₁₀
                                        && 1 <= i₁₀
                                        && i₁₀ < 1)
                                   ==> (exists j₈: int, k₉: int, i₁₀: int ::
                                          j₈ <= k₉
                                          && -10000 < k₉
                                          && k₉ < 10000
                                          && -10000 < j₈
                                          && j₈ < 10000
                                          && i₁₀ < N
                                          && x₁₁ == i₁₀
                                          && 1 <= i₁₀
                                          && i₁₀ < 1
                                          && a[x₁₁] == k₉)))
                          && (forall x₁₁: int ::
                                (!((exists i₁₀: int ::
                                        x₁₁ == i₁₀
                                        && 1 <= i₁₀
                                        && i₁₀ < 1)
                                )
                                   ==> a[x₁₁] == a[x₁₁]))
                          && (forall x₁₂: int ::
                                ((exists i₁₀: int ::
                                        x₁₂ == i₁₀
                                        && 1 <= i₁₀
                                        && i₁₀ < 1)
                                   ==> (exists j₈: int, k₉: int, i₁₀: int ::
                                          j₈ <= k₉
                                          && -10000 < k₉
                                          && k₉ < 10000
                                          && -10000 < j₈
                                          && j₈ < 10000
                                          && i₁₀ < N
                                          && x₁₂ == i₁₀
                                          && 1 <= i₁₀
                                          && i₁₀ < 1
                                          && b[x₁₂] == j₈)))
                          && (forall x₁₂: int ::
                                (!((exists i₁₀: int ::
                                        x₁₂ == i₁₀
                                        && 1 <= i₁₀
                                        && i₁₀ < 1)
                                )
                                   ==> b[x₁₂] == b[x₁₂]))
                          && (forall i₁₀: int ::
                                (  1 <= i₁₀
                                  && i₁₀ < 1
                                   ==> i₁₀ < N))
                          && (forall a₂₄: [int]int, b₂₅: [int]int, i₂₆: int ::
                                (  true
                                  && 1 <= i₂₆
                                  && i₂₆ <= N
                                  && (forall x₁₁: int ::
                                        ((exists i₁₀: int ::
                                                x₁₁ == i₁₀
                                                && 1 <= i₁₀
                                                && i₁₀ < i₂₆)
                                           ==> (exists j₈: int, k₉: int, i₁₀: int ::
                                                  j₈ <= k₉
                                                  && -10000 < k₉
                                                  && k₉ < 10000
                                                  && -10000 < j₈
                                                  && j₈ < 10000
                                                  && i₁₀ < N
                                                  && x₁₁ == i₁₀
                                                  && 1 <= i₁₀
                                                  && i₁₀ < i₂₆
                                                  && a₂₄[x₁₁] == k₉)))
                                  && (forall x₁₁: int ::
                                        (!((exists i₁₀: int ::
                                                x₁₁ == i₁₀
                                                && 1 <= i₁₀
                                                && i₁₀ < i₂₆)
                                        )
                                           ==> a₂₄[x₁₁] == a[x₁₁]))
                                  && (forall x₁₂: int ::
                                        ((exists i₁₀: int ::
                                                x₁₂ == i₁₀
                                                && 1 <= i₁₀
                                                && i₁₀ < i₂₆)
                                           ==> (exists j₈: int, k₉: int, i₁₀: int ::
                                                  j₈ <= k₉
                                                  && -10000 < k₉
                                                  && k₉ < 10000
                                                  && -10000 < j₈
                                                  && j₈ < 10000
                                                  && i₁₀ < N
                                                  && x₁₂ == i₁₀
                                                  && 1 <= i₁₀
                                                  && i₁₀ < i₂₆
                                                  && b₂₅[x₁₂] == j₈)))
                                  && (forall x₁₂: int ::
                                        (!((exists i₁₀: int ::
                                                x₁₂ == i₁₀
                                                && 1 <= i₁₀
                                                && i₁₀ < i₂₆)
                                        )
                                           ==> b₂₅[x₁₂] == b[x₁₂]))
                                  && (forall i₁₀: int ::
                                        (  1 <= i₁₀
                                          && i₁₀ < i₂₆
                                           ==> i₁₀ < N))
                                   ==> (i₂₆ < N
                                       ==> (forall j: int ::
                                            (forall k: int ::
                                                    true
                                                    && (  -10000 < j
                                                      && j < 10000
                                                       ==> true
                                                        && (  -10000 < k
                                                          && k < 10000
                                                           ==> true
                                                            && (j <= k
                                                               ==> true
                                                                && 1 <= i₂₆ + 1
                                                                && i₂₆ + 1 <= N
                                                                && (forall x₁₁: int ::
                                                                      ((exists i₁₀: int ::
                                                                              x₁₁ == i₁₀
                                                                              && 1 <= i₁₀
                                                                              && i₁₀ < i₂₆ + 1)
                                                                         ==> (exists j₈: int, k₉: int, i₁₀: int ::
                                                                                j₈ <= k₉
                                                                                && -10000 < k₉
                                                                                && k₉ < 10000
                                                                                && -10000 < j₈
                                                                                && j₈ < 10000
                                                                                && i₁₀ < N
                                                                                && x₁₁ == i₁₀
                                                                                && 1 <= i₁₀
                                                                                && i₁₀ < i₂₆ + 1
                                                                                && a₂₄[i₂₆ := k][x₁₁] == k₉)))
                                                                && (forall x₁₁: int ::
                                                                      (!((exists i₁₀: int ::
                                                                              x₁₁ == i₁₀
                                                                              && 1 <= i₁₀
                                                                              && i₁₀ < i₂₆ + 1)
                                                                      )
                                                                         ==> a₂₄[i₂₆ := k][x₁₁] == a[x₁₁]))
                                                                && (forall x₁₂: int ::
                                                                      ((exists i₁₀: int ::
                                                                              x₁₂ == i₁₀
                                                                              && 1 <= i₁₀
                                                                              && i₁₀ < i₂₆ + 1)
                                                                         ==> (exists j₈: int, k₉: int, i₁₀: int ::
                                                                                j₈ <= k₉
                                                                                && -10000 < k₉
                                                                                && k₉ < 10000
                                                                                && -10000 < j₈
                                                                                && j₈ < 10000
                                                                                && i₁₀ < N
                                                                                && x₁₂ == i₁₀
                                                                                && 1 <= i₁₀
                                                                                && i₁₀ < i₂₆ + 1
                                                                                && b₂₅[i₂₆ := j][x₁₂] == j₈)))
                                                                && (forall x₁₂: int ::
                                                                      (!((exists i₁₀: int ::
                                                                              x₁₂ == i₁₀
                                                                              && 1 <= i₁₀
                                                                              && i₁₀ < i₂₆ + 1)
                                                                      )
                                                                         ==> b₂₅[i₂₆ := j][x₁₂] == b[x₁₂]))
                                                                && (forall i₁₀: int ::
                                                                      (  1 <= i₁₀
                                                                        && i₁₀ < i₂₆ + 1
                                                                         ==> i₁₀ < N))
                                                                && true
                                                                && (true
                                                                   ==> true)))))))
                                    && (!(i₂₆ < N
                                    )
                                       ==> true
                                        && (true
                                           ==> true
                                            && 0 <= 0
                                            && 0 <= N
                                            && (forall x₁₇: int ::
                                                  ((exists i₁₆: int ::
                                                          x₁₇ == i₁₆
                                                          && 0 <= i₁₆
                                                          && i₁₆ < 0)
                                                     ==> (exists i₁₆: int ::
                                                            i₁₆ < N
                                                            && x₁₇ == i₁₆
                                                            && 0 <= i₁₆
                                                            && i₁₆ < 0
                                                            && a₂₄[x₁₇] == 1 + a₂₄[i₁₆])))
                                            && (forall x₁₇: int ::
                                                  (!((exists i₁₆: int ::
                                                          x₁₇ == i₁₆
                                                          && 0 <= i₁₆
                                                          && i₁₆ < 0)
                                                  )
                                                     ==> a₂₄[x₁₇] == a₂₄[x₁₇]))
                                            && (forall x₁₈: int ::
                                                  ((exists i₁₆: int ::
                                                          x₁₈ == i₁₆
                                                          && 0 <= i₁₆
                                                          && i₁₆ < 0)
                                                     ==> (exists i₁₆: int ::
                                                            i₁₆ < N
                                                            && x₁₈ == i₁₆
                                                            && 0 <= i₁₆
                                                            && i₁₆ < 0
                                                            && b₂₅[x₁₈] == 1 + b₂₅[i₁₆])))
                                            && (forall x₁₈: int ::
                                                  (!((exists i₁₆: int ::
                                                          x₁₈ == i₁₆
                                                          && 0 <= i₁₆
                                                          && i₁₆ < 0)
                                                  )
                                                     ==> b₂₅[x₁₈] == b₂₅[x₁₈]))
                                            && (forall i₁₆: int ::
                                                  (  0 <= i₁₆
                                                    && i₁₆ < 0
                                                     ==> i₁₆ < N))
                                            && (forall a₂₇: [int]int, b₂₈: [int]int, i₂₉: int ::
                                                  (  true
                                                    && 0 <= i₂₉
                                                    && i₂₉ <= N
                                                    && (forall x₁₇: int ::
                                                          ((exists i₁₆: int ::
                                                                  x₁₇ == i₁₆
                                                                  && 0 <= i₁₆
                                                                  && i₁₆ < i₂₉)
                                                             ==> (exists i₁₆: int ::
                                                                    i₁₆ < N
                                                                    && x₁₇ == i₁₆
                                                                    && 0 <= i₁₆
                                                                    && i₁₆ < i₂₉
                                                                    && a₂₇[x₁₇] == 1 + a₂₄[i₁₆])))
                                                    && (forall x₁₇: int ::
                                                          (!((exists i₁₆: int ::
                                                                  x₁₇ == i₁₆
                                                                  && 0 <= i₁₆
                                                                  && i₁₆ < i₂₉)
                                                          )
                                                             ==> a₂₇[x₁₇] == a₂₄[x₁₇]))
                                                    && (forall x₁₈: int ::
                                                          ((exists i₁₆: int ::
                                                                  x₁₈ == i₁₆
                                                                  && 0 <= i₁₆
                                                                  && i₁₆ < i₂₉)
                                                             ==> (exists i₁₆: int ::
                                                                    i₁₆ < N
                                                                    && x₁₈ == i₁₆
                                                                    && 0 <= i₁₆
                                                                    && i₁₆ < i₂₉
                                                                    && b₂₈[x₁₈] == 1 + b₂₅[i₁₆])))
                                                    && (forall x₁₈: int ::
                                                          (!((exists i₁₆: int ::
                                                                  x₁₈ == i₁₆
                                                                  && 0 <= i₁₆
                                                                  && i₁₆ < i₂₉)
                                                          )
                                                             ==> b₂₈[x₁₈] == b₂₅[x₁₈]))
                                                    && (forall i₁₆: int ::
                                                          (  0 <= i₁₆
                                                            && i₁₆ < i₂₉
                                                             ==> i₁₆ < N))
                                                     ==> (i₂₉ < N
                                                         ==> true
                                                          && 0 <= i₂₉ + 1
                                                          && i₂₉ + 1 <= N
                                                          && (forall x₁₇: int ::
                                                                ((exists i₁₆: int ::
                                                                        x₁₇ == i₁₆
                                                                        && 0 <= i₁₆
                                                                        && i₁₆ < i₂₉ + 1)
                                                                   ==> (exists i₁₆: int ::
                                                                          i₁₆ < N
                                                                          && x₁₇ == i₁₆
                                                                          && 0 <= i₁₆
                                                                          && i₁₆ < i₂₉ + 1
                                                                          && a₂₇[i₂₉ := a₂₇[i₂₉] + 1][x₁₇] == 1 + a₂₄[i₁₆])))
                                                          && (forall x₁₇: int ::
                                                                (!((exists i₁₆: int ::
                                                                        x₁₇ == i₁₆
                                                                        && 0 <= i₁₆
                                                                        && i₁₆ < i₂₉ + 1)
                                                                )
                                                                   ==> a₂₇[i₂₉ := a₂₇[i₂₉] + 1][x₁₇] == a₂₄[x₁₇]))
                                                          && (forall x₁₈: int ::
                                                                ((exists i₁₆: int ::
                                                                        x₁₈ == i₁₆
                                                                        && 0 <= i₁₆
                                                                        && i₁₆ < i₂₉ + 1)
                                                                   ==> (exists i₁₆: int ::
                                                                          i₁₆ < N
                                                                          && x₁₈ == i₁₆
                                                                          && 0 <= i₁₆
                                                                          && i₁₆ < i₂₉ + 1
                                                                          && b₂₈[i₂₉ := b₂₈[i₂₉] + 1][x₁₈] == 1 + b₂₅[i₁₆])))
                                                          && (forall x₁₈: int ::
                                                                (!((exists i₁₆: int ::
                                                                        x₁₈ == i₁₆
                                                                        && 0 <= i₁₆
                                                                        && i₁₆ < i₂₉ + 1)
                                                                )
                                                                   ==> b₂₈[i₂₉ := b₂₈[i₂₉] + 1][x₁₈] == b₂₅[x₁₈]))
                                                          && (forall i₁₆: int ::
                                                                (  0 <= i₁₆
                                                                  && i₁₆ < i₂₉ + 1
                                                                   ==> i₁₆ < N))
                                                          && true
                                                          && (true
                                                             ==> true))
                                                      && (!(i₂₉ < N
                                                      )
                                                         ==> true
                                                          && (true
                                                             ==> true
                                                              && 1 <= 1
                                                              && 1 <= N
                                                              && (forall i₂₂: int ::
                                                                    (  1 <= i₂₂
                                                                      && i₂₂ < 1
                                                                       ==> i₂₂ < N))
                                                              && (forall i₃₀: int ::
                                                                    (  true
                                                                      && 1 <= i₃₀
                                                                      && i₃₀ <= N
                                                                      && (forall i₂₂: int ::
                                                                            (  1 <= i₂₂
                                                                              && i₂₂ < i₃₀
                                                                               ==> i₂₂ < N))
                                                                       ==> (i₃₀ < N
                                                                           ==> b₂₈[i₃₀] <= a₂₇[i₃₀]
                                                                            && (true
                                                                               ==> true
                                                                                && 1 <= i₃₀ + 1
                                                                                && i₃₀ + 1 <= N
                                                                                && (forall i₂₂: int ::
                                                                                      (  1 <= i₂₂
                                                                                        && i₂₂ < i₃₀ + 1
                                                                                         ==> i₂₂ < N))
                                                                                && true
                                                                                && (true
                                                                                   ==> true)))
                                                                        && (!(i₃₀ < N
                                                                        )
                                                                           ==> true
                                                                            && (true
                                                                               ==> true)))))))))))))))));


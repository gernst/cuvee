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
                          && (forall x₁₀: int ::
                                ((exists i₉: int ::
                                        x₁₀ == i₉
                                        && 1 <= i₉
                                        && i₉ < 1)
                                   ==> (exists j₈: int, i₉: int ::
                                          1 <= j₈
                                          && i₉ < N
                                          && x₁₀ == i₉
                                          && 1 <= i₉
                                          && i₉ < 1
                                          && a[x₁₀] == j₈)))
                          && (forall x₁₀: int ::
                                (!((exists i₉: int ::
                                        x₁₀ == i₉
                                        && 1 <= i₉
                                        && i₉ < 1)
                                )
                                   ==> a[x₁₀] == a[x₁₀]))
                          && (forall i₉: int ::
                                (  1 <= i₉
                                  && i₉ < 1
                                   ==> i₉ < N))
                          && (forall a₁₉: [int]int, i₂₀: int ::
                                (  true
                                  && 1 <= i₂₀
                                  && i₂₀ <= N
                                  && (forall x₁₀: int ::
                                        ((exists i₉: int ::
                                                x₁₀ == i₉
                                                && 1 <= i₉
                                                && i₉ < i₂₀)
                                           ==> (exists j₈: int, i₉: int ::
                                                  1 <= j₈
                                                  && i₉ < N
                                                  && x₁₀ == i₉
                                                  && 1 <= i₉
                                                  && i₉ < i₂₀
                                                  && a₁₉[x₁₀] == j₈)))
                                  && (forall x₁₀: int ::
                                        (!((exists i₉: int ::
                                                x₁₀ == i₉
                                                && 1 <= i₉
                                                && i₉ < i₂₀)
                                        )
                                           ==> a₁₉[x₁₀] == a[x₁₀]))
                                  && (forall i₉: int ::
                                        (  1 <= i₉
                                          && i₉ < i₂₀
                                           ==> i₉ < N))
                                   ==> (i₂₀ < N
                                       ==> (forall j: int ::
                                              true
                                              && (1 <= j
                                                 ==> true
                                                  && 1 <= i₂₀ + 1
                                                  && i₂₀ + 1 <= N
                                                  && (forall x₁₀: int ::
                                                        ((exists i₉: int ::
                                                                x₁₀ == i₉
                                                                && 1 <= i₉
                                                                && i₉ < i₂₀ + 1)
                                                           ==> (exists j₈: int, i₉: int ::
                                                                  1 <= j₈
                                                                  && i₉ < N
                                                                  && x₁₀ == i₉
                                                                  && 1 <= i₉
                                                                  && i₉ < i₂₀ + 1
                                                                  && a₁₉[i₂₀ := j][x₁₀] == j₈)))
                                                  && (forall x₁₀: int ::
                                                        (!((exists i₉: int ::
                                                                x₁₀ == i₉
                                                                && 1 <= i₉
                                                                && i₉ < i₂₀ + 1)
                                                        )
                                                           ==> a₁₉[i₂₀ := j][x₁₀] == a[x₁₀]))
                                                  && (forall i₉: int ::
                                                        (  1 <= i₉
                                                          && i₉ < i₂₀ + 1
                                                           ==> i₉ < N))
                                                  && true
                                                  && (true
                                                     ==> true))))
                                    && (!(i₂₀ < N
                                    )
                                       ==> true
                                        && (true
                                           ==> true
                                            && 0 <= 0
                                            && 0 <= N
                                            && (forall x₁₄: int ::
                                                  ((exists i₁₃: int ::
                                                          x₁₄ == i₁₃
                                                          && 0 <= i₁₃
                                                          && i₁₃ < 0)
                                                     ==> (exists i₁₃: int ::
                                                            i₁₃ < N
                                                            && x₁₄ == i₁₃
                                                            && 0 <= i₁₃
                                                            && i₁₃ < 0
                                                            && b[x₁₄] == a₁₉[i₁₃])))
                                            && (forall x₁₄: int ::
                                                  (!((exists i₁₃: int ::
                                                          x₁₄ == i₁₃
                                                          && 0 <= i₁₃
                                                          && i₁₃ < 0)
                                                  )
                                                     ==> b[x₁₄] == b[x₁₄]))
                                            && (forall i₁₃: int ::
                                                  (  0 <= i₁₃
                                                    && i₁₃ < 0
                                                     ==> i₁₃ < N))
                                            && (forall b₂₁: [int]int, i₂₂: int ::
                                                  (  true
                                                    && 0 <= i₂₂
                                                    && i₂₂ <= N
                                                    && (forall x₁₄: int ::
                                                          ((exists i₁₃: int ::
                                                                  x₁₄ == i₁₃
                                                                  && 0 <= i₁₃
                                                                  && i₁₃ < i₂₂)
                                                             ==> (exists i₁₃: int ::
                                                                    i₁₃ < N
                                                                    && x₁₄ == i₁₃
                                                                    && 0 <= i₁₃
                                                                    && i₁₃ < i₂₂
                                                                    && b₂₁[x₁₄] == a₁₉[i₁₃])))
                                                    && (forall x₁₄: int ::
                                                          (!((exists i₁₃: int ::
                                                                  x₁₄ == i₁₃
                                                                  && 0 <= i₁₃
                                                                  && i₁₃ < i₂₂)
                                                          )
                                                             ==> b₂₁[x₁₄] == b[x₁₄]))
                                                    && (forall i₁₃: int ::
                                                          (  0 <= i₁₃
                                                            && i₁₃ < i₂₂
                                                             ==> i₁₃ < N))
                                                     ==> (i₂₂ < N
                                                         ==> true
                                                          && 0 <= i₂₂ + 1
                                                          && i₂₂ + 1 <= N
                                                          && (forall x₁₄: int ::
                                                                ((exists i₁₃: int ::
                                                                        x₁₄ == i₁₃
                                                                        && 0 <= i₁₃
                                                                        && i₁₃ < i₂₂ + 1)
                                                                   ==> (exists i₁₃: int ::
                                                                          i₁₃ < N
                                                                          && x₁₄ == i₁₃
                                                                          && 0 <= i₁₃
                                                                          && i₁₃ < i₂₂ + 1
                                                                          && b₂₁[i₂₂ := a₁₉[i₂₂]][x₁₄] == a₁₉[i₁₃])))
                                                          && (forall x₁₄: int ::
                                                                (!((exists i₁₃: int ::
                                                                        x₁₄ == i₁₃
                                                                        && 0 <= i₁₃
                                                                        && i₁₃ < i₂₂ + 1)
                                                                )
                                                                   ==> b₂₁[i₂₂ := a₁₉[i₂₂]][x₁₄] == b[x₁₄]))
                                                          && (forall i₁₃: int ::
                                                                (  0 <= i₁₃
                                                                  && i₁₃ < i₂₂ + 1
                                                                   ==> i₁₃ < N))
                                                          && true
                                                          && (true
                                                             ==> true))
                                                      && (!(i₂₂ < N
                                                      )
                                                         ==> true
                                                          && (true
                                                             ==> true
                                                              && 1 <= 1
                                                              && 1 <= N
                                                              && (forall i₁₇: int ::
                                                                    (  1 <= i₁₇
                                                                      && i₁₇ < 1
                                                                       ==> i₁₇ < N))
                                                              && (forall i₂₃: int ::
                                                                    (  true
                                                                      && 1 <= i₂₃
                                                                      && i₂₃ <= N
                                                                      && (forall i₁₇: int ::
                                                                            (  1 <= i₁₇
                                                                              && i₁₇ < i₂₃
                                                                               ==> i₁₇ < N))
                                                                       ==> (i₂₃ < N
                                                                           ==> 1 <= b₂₁[i₂₃]
                                                                            && (true
                                                                               ==> true
                                                                                && 1 <= i₂₃ + 1
                                                                                && i₂₃ + 1 <= N
                                                                                && (forall i₁₇: int ::
                                                                                      (  1 <= i₁₇
                                                                                        && i₁₇ < i₂₃ + 1
                                                                                         ==> i₁₇ < N))
                                                                                && true
                                                                                && (true
                                                                                   ==> true)))
                                                                        && (!(i₂₃ < N
                                                                        )
                                                                           ==> true
                                                                            && (true
                                                                               ==> true)))))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> (forall N: int ::
        (forall a: [int]int ::
                true
                && (0 < N
                   ==> true
                    && 1 <= 1
                    && 1 <= N
                    && (forall x₈: int ::
                          ((exists i₇: int ::
                                  x₈ == i₇
                                  && 1 <= i₇
                                  && i₇ < 1)
                             ==> (exists i₇: int ::
                                    i₇ < N
                                    && x₈ == i₇
                                    && 1 <= i₇
                                    && i₇ < 1
                                    && a[x₈] == 1)))
                    && (forall x₈: int ::
                          (!((exists i₇: int ::
                                  x₈ == i₇
                                  && 1 <= i₇
                                  && i₇ < 1)
                          )
                             ==> a[x₈] == a[x₈]))
                    && (forall i₇: int ::
                          (  1 <= i₇
                            && i₇ < 1
                             ==> i₇ < N))
                    && (forall a₁₇: [int]int, i₁₈: int ::
                          (  true
                            && 1 <= i₁₈
                            && i₁₈ <= N
                            && (forall x₈: int ::
                                  ((exists i₇: int ::
                                          x₈ == i₇
                                          && 1 <= i₇
                                          && i₇ < i₁₈)
                                     ==> (exists i₇: int ::
                                            i₇ < N
                                            && x₈ == i₇
                                            && 1 <= i₇
                                            && i₇ < i₁₈
                                            && a₁₇[x₈] == 1)))
                            && (forall x₈: int ::
                                  (!((exists i₇: int ::
                                          x₈ == i₇
                                          && 1 <= i₇
                                          && i₇ < i₁₈)
                                  )
                                     ==> a₁₇[x₈] == a[x₈]))
                            && (forall i₇: int ::
                                  (  1 <= i₇
                                    && i₇ < i₁₈
                                     ==> i₇ < N))
                             ==> (i₁₈ < N
                                 ==> true
                                  && 1 <= i₁₈ + 1
                                  && i₁₈ + 1 <= N
                                  && (forall x₈: int ::
                                        ((exists i₇: int ::
                                                x₈ == i₇
                                                && 1 <= i₇
                                                && i₇ < i₁₈ + 1)
                                           ==> (exists i₇: int ::
                                                  i₇ < N
                                                  && x₈ == i₇
                                                  && 1 <= i₇
                                                  && i₇ < i₁₈ + 1
                                                  && a₁₇[i₁₈ := 1][x₈] == 1)))
                                  && (forall x₈: int ::
                                        (!((exists i₇: int ::
                                                x₈ == i₇
                                                && 1 <= i₇
                                                && i₇ < i₁₈ + 1)
                                        )
                                           ==> a₁₇[i₁₈ := 1][x₈] == a[x₈]))
                                  && (forall i₇: int ::
                                        (  1 <= i₇
                                          && i₇ < i₁₈ + 1
                                           ==> i₇ < N))
                                  && true
                                  && (true
                                     ==> true))
                              && (!(i₁₈ < N
                              )
                                 ==> true
                                  && (true
                                     ==> true
                                      && N - 1 <= N - 1
                                      && 0 <= 1 + N - 1
                                      && (forall x₁₂: int ::
                                            ((exists i₁₁: int ::
                                                    x₁₂ == i₁₁
                                                    && N - 1 < i₁₁
                                                    && i₁₁ <= N - 1)
                                               ==> (exists i₁₁: int ::
                                                      0 <= i₁₁
                                                      && x₁₂ == i₁₁
                                                      && N - 1 < i₁₁
                                                      && i₁₁ <= N - 1
                                                      && a₁₇[x₁₂] == -1 + a₁₇[i₁₁])))
                                      && (forall x₁₂: int ::
                                            (!((exists i₁₁: int ::
                                                    x₁₂ == i₁₁
                                                    && N - 1 < i₁₁
                                                    && i₁₁ <= N - 1)
                                            )
                                               ==> a₁₇[x₁₂] == a₁₇[x₁₂]))
                                      && (forall i₁₁: int ::
                                            (  N - 1 < i₁₁
                                              && i₁₁ <= N - 1
                                               ==> 0 <= i₁₁))
                                      && (forall a₁₉: [int]int, i₂₀: int ::
                                            (  true
                                              && i₂₀ <= N - 1
                                              && 0 <= 1 + i₂₀
                                              && (forall x₁₂: int ::
                                                    ((exists i₁₁: int ::
                                                            x₁₂ == i₁₁
                                                            && i₂₀ < i₁₁
                                                            && i₁₁ <= N - 1)
                                                       ==> (exists i₁₁: int ::
                                                              0 <= i₁₁
                                                              && x₁₂ == i₁₁
                                                              && i₂₀ < i₁₁
                                                              && i₁₁ <= N - 1
                                                              && a₁₉[x₁₂] == -1 + a₁₇[i₁₁])))
                                              && (forall x₁₂: int ::
                                                    (!((exists i₁₁: int ::
                                                            x₁₂ == i₁₁
                                                            && i₂₀ < i₁₁
                                                            && i₁₁ <= N - 1)
                                                    )
                                                       ==> a₁₉[x₁₂] == a₁₇[x₁₂]))
                                              && (forall i₁₁: int ::
                                                    (  i₂₀ < i₁₁
                                                      && i₁₁ <= N - 1
                                                       ==> 0 <= i₁₁))
                                               ==> (0 <= i₂₀
                                                   ==> true
                                                    && i₂₀ - 1 <= N - 1
                                                    && 0 <= 1 + i₂₀ - 1
                                                    && (forall x₁₂: int ::
                                                          ((exists i₁₁: int ::
                                                                  x₁₂ == i₁₁
                                                                  && i₂₀ - 1 < i₁₁
                                                                  && i₁₁ <= N - 1)
                                                             ==> (exists i₁₁: int ::
                                                                    0 <= i₁₁
                                                                    && x₁₂ == i₁₁
                                                                    && i₂₀ - 1 < i₁₁
                                                                    && i₁₁ <= N - 1
                                                                    && a₁₉[i₂₀ := a₁₉[i₂₀] - 1][x₁₂] == -1 + a₁₇[i₁₁])))
                                                    && (forall x₁₂: int ::
                                                          (!((exists i₁₁: int ::
                                                                  x₁₂ == i₁₁
                                                                  && i₂₀ - 1 < i₁₁
                                                                  && i₁₁ <= N - 1)
                                                          )
                                                             ==> a₁₉[i₂₀ := a₁₉[i₂₀] - 1][x₁₂] == a₁₇[x₁₂]))
                                                    && (forall i₁₁: int ::
                                                          (  i₂₀ - 1 < i₁₁
                                                            && i₁₁ <= N - 1
                                                             ==> 0 <= i₁₁))
                                                    && true
                                                    && (true
                                                       ==> true))
                                                && (!(0 <= i₂₀
                                                )
                                                   ==> true
                                                    && (true
                                                       ==> true
                                                        && 1 <= 1
                                                        && 1 <= N
                                                        && (forall i₁₅: int ::
                                                              (  1 <= i₁₅
                                                                && i₁₅ < 1
                                                                 ==> i₁₅ < N))
                                                        && (forall i₂₁: int ::
                                                              (  true
                                                                && 1 <= i₂₁
                                                                && i₂₁ <= N
                                                                && (forall i₁₅: int ::
                                                                      (  1 <= i₁₅
                                                                        && i₁₅ < i₂₁
                                                                         ==> i₁₅ < N))
                                                                 ==> (i₂₁ < N
                                                                     ==> a₁₉[i₂₁] == 0
                                                                      && (true
                                                                         ==> true
                                                                          && 1 <= i₂₁ + 1
                                                                          && i₂₁ + 1 <= N
                                                                          && (forall i₁₅: int ::
                                                                                (  1 <= i₁₅
                                                                                  && i₁₅ < i₂₁ + 1
                                                                                   ==> i₁₅ < N))
                                                                          && true
                                                                          && (true
                                                                             ==> true)))
                                                                  && (!(i₂₁ < N
                                                                  )
                                                                     ==> true
                                                                      && (true
                                                                         ==> true))))))))))))))));


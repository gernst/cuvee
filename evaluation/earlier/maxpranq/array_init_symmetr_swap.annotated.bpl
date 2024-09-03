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
                                   ==> (exists x₈: int, i₉: int ::
                                          x₈ < 10000
                                          && i₉ < N
                                          && x₁₀ == i₉
                                          && 1 <= i₉
                                          && i₉ < 1
                                          && a[x₁₀] == x₈)))
                          && (forall x₁₀: int ::
                                (!((exists i₉: int ::
                                        x₁₀ == i₉
                                        && 1 <= i₉
                                        && i₉ < 1)
                                )
                                   ==> a[x₁₀] == a[x₁₀]))
                          && (forall x₁₁: int ::
                                ((exists i₉: int ::
                                        x₁₁ == i₉
                                        && 1 <= i₉
                                        && i₉ < 1)
                                   ==> (exists x₈: int, i₉: int ::
                                          x₈ < 10000
                                          && i₉ < N
                                          && x₁₁ == i₉
                                          && 1 <= i₉
                                          && i₉ < 1
                                          && b[x₁₁] == -x₈)))
                          && (forall x₁₁: int ::
                                (!((exists i₉: int ::
                                        x₁₁ == i₉
                                        && 1 <= i₉
                                        && i₉ < 1)
                                )
                                   ==> b[x₁₁] == b[x₁₁]))
                          && (forall i₉: int ::
                                (  i₉ <= i₉
                                  && 1 <= i₉
                                  && i₉ < 1
                                   ==> i₉ < N))
                          && (forall a₂₃: [int]int, b₂₄: [int]int, i₂₅: int ::
                                (  true
                                  && 1 <= i₂₅
                                  && i₂₅ <= N
                                  && (forall x₁₀: int ::
                                        ((exists i₉: int ::
                                                x₁₀ == i₉
                                                && 1 <= i₉
                                                && i₉ < i₂₅)
                                           ==> (exists x₈: int, i₉: int ::
                                                  x₈ < 10000
                                                  && i₉ < N
                                                  && x₁₀ == i₉
                                                  && 1 <= i₉
                                                  && i₉ < i₂₅
                                                  && a₂₃[x₁₀] == x₈)))
                                  && (forall x₁₀: int ::
                                        (!((exists i₉: int ::
                                                x₁₀ == i₉
                                                && 1 <= i₉
                                                && i₉ < i₂₅)
                                        )
                                           ==> a₂₃[x₁₀] == a[x₁₀]))
                                  && (forall x₁₁: int ::
                                        ((exists i₉: int ::
                                                x₁₁ == i₉
                                                && 1 <= i₉
                                                && i₉ < i₂₅)
                                           ==> (exists x₈: int, i₉: int ::
                                                  x₈ < 10000
                                                  && i₉ < N
                                                  && x₁₁ == i₉
                                                  && 1 <= i₉
                                                  && i₉ < i₂₅
                                                  && b₂₄[x₁₁] == -x₈)))
                                  && (forall x₁₁: int ::
                                        (!((exists i₉: int ::
                                                x₁₁ == i₉
                                                && 1 <= i₉
                                                && i₉ < i₂₅)
                                        )
                                           ==> b₂₄[x₁₁] == b[x₁₁]))
                                  && (forall i₉: int ::
                                        (  i₉ <= i₉
                                          && 1 <= i₉
                                          && i₉ < i₂₅
                                           ==> i₉ < N))
                                   ==> (i₂₅ < N
                                       ==> (forall x: int ::
                                              true
                                              && (x < 10000
                                                 ==> true
                                                  && 1 <= i₂₅ + 1
                                                  && i₂₅ + 1 <= N
                                                  && (forall x₁₀: int ::
                                                        ((exists i₉: int ::
                                                                x₁₀ == i₉
                                                                && 1 <= i₉
                                                                && i₉ < i₂₅ + 1)
                                                           ==> (exists x₈: int, i₉: int ::
                                                                  x₈ < 10000
                                                                  && i₉ < N
                                                                  && x₁₀ == i₉
                                                                  && 1 <= i₉
                                                                  && i₉ < i₂₅ + 1
                                                                  && a₂₃[i₂₅ := x][x₁₀] == x₈)))
                                                  && (forall x₁₀: int ::
                                                        (!((exists i₉: int ::
                                                                x₁₀ == i₉
                                                                && 1 <= i₉
                                                                && i₉ < i₂₅ + 1)
                                                        )
                                                           ==> a₂₃[i₂₅ := x][x₁₀] == a[x₁₀]))
                                                  && (forall x₁₁: int ::
                                                        ((exists i₉: int ::
                                                                x₁₁ == i₉
                                                                && 1 <= i₉
                                                                && i₉ < i₂₅ + 1)
                                                           ==> (exists x₈: int, i₉: int ::
                                                                  x₈ < 10000
                                                                  && i₉ < N
                                                                  && x₁₁ == i₉
                                                                  && 1 <= i₉
                                                                  && i₉ < i₂₅ + 1
                                                                  && b₂₄[i₂₅ := -x][x₁₁] == -x₈)))
                                                  && (forall x₁₁: int ::
                                                        (!((exists i₉: int ::
                                                                x₁₁ == i₉
                                                                && 1 <= i₉
                                                                && i₉ < i₂₅ + 1)
                                                        )
                                                           ==> b₂₄[i₂₅ := -x][x₁₁] == b[x₁₁]))
                                                  && (forall i₉: int ::
                                                        (  i₉ <= i₉
                                                          && 1 <= i₉
                                                          && i₉ < i₂₅ + 1
                                                           ==> i₉ < N))
                                                  && true
                                                  && (true
                                                     ==> true))))
                                    && (!(i₂₅ < N
                                    )
                                       ==> true
                                        && (true
                                           ==> true
                                            && 0 <= 0
                                            && 0 <= N
                                            && (forall x₁₆: int ::
                                                  ((exists i₁₅: int ::
                                                          x₁₆ == i₁₅
                                                          && 0 <= i₁₅
                                                          && i₁₅ < 0)
                                                     ==> (exists i₁₅: int ::
                                                            i₁₅ < N
                                                            && x₁₆ == i₁₅
                                                            && 0 <= i₁₅
                                                            && i₁₅ < 0
                                                            && a₂₃[x₁₆] == -b₂₄[i₁₅])))
                                            && (forall x₁₆: int ::
                                                  (!((exists i₁₅: int ::
                                                          x₁₆ == i₁₅
                                                          && 0 <= i₁₅
                                                          && i₁₅ < 0)
                                                  )
                                                     ==> a₂₃[x₁₆] == a₂₃[x₁₆]))
                                            && (forall x₁₇: int ::
                                                  ((exists i₁₅: int ::
                                                          x₁₇ == i₁₅
                                                          && 0 <= i₁₅
                                                          && i₁₅ < 0)
                                                     ==> (exists i₁₅: int ::
                                                            i₁₅ < N
                                                            && x₁₇ == i₁₅
                                                            && 0 <= i₁₅
                                                            && i₁₅ < 0
                                                            && b₂₄[x₁₇] == a₂₃[i₁₅])))
                                            && (forall x₁₇: int ::
                                                  (!((exists i₁₅: int ::
                                                          x₁₇ == i₁₅
                                                          && 0 <= i₁₅
                                                          && i₁₅ < 0)
                                                  )
                                                     ==> b₂₄[x₁₇] == b₂₄[x₁₇]))
                                            && (forall i₁₅: int ::
                                                  (  i₁₅ <= i₁₅
                                                    && 0 <= i₁₅
                                                    && i₁₅ < 0
                                                     ==> i₁₅ < N))
                                            && (forall a₂₆: [int]int, b₂₇: [int]int, i₂₈: int ::
                                                  (  true
                                                    && 0 <= i₂₈
                                                    && i₂₈ <= N
                                                    && (forall x₁₆: int ::
                                                          ((exists i₁₅: int ::
                                                                  x₁₆ == i₁₅
                                                                  && 0 <= i₁₅
                                                                  && i₁₅ < i₂₈)
                                                             ==> (exists i₁₅: int ::
                                                                    i₁₅ < N
                                                                    && x₁₆ == i₁₅
                                                                    && 0 <= i₁₅
                                                                    && i₁₅ < i₂₈
                                                                    && a₂₆[x₁₆] == -b₂₄[i₁₅])))
                                                    && (forall x₁₆: int ::
                                                          (!((exists i₁₅: int ::
                                                                  x₁₆ == i₁₅
                                                                  && 0 <= i₁₅
                                                                  && i₁₅ < i₂₈)
                                                          )
                                                             ==> a₂₆[x₁₆] == a₂₃[x₁₆]))
                                                    && (forall x₁₇: int ::
                                                          ((exists i₁₅: int ::
                                                                  x₁₇ == i₁₅
                                                                  && 0 <= i₁₅
                                                                  && i₁₅ < i₂₈)
                                                             ==> (exists i₁₅: int ::
                                                                    i₁₅ < N
                                                                    && x₁₇ == i₁₅
                                                                    && 0 <= i₁₅
                                                                    && i₁₅ < i₂₈
                                                                    && b₂₇[x₁₇] == a₂₃[i₁₅])))
                                                    && (forall x₁₇: int ::
                                                          (!((exists i₁₅: int ::
                                                                  x₁₇ == i₁₅
                                                                  && 0 <= i₁₅
                                                                  && i₁₅ < i₂₈)
                                                          )
                                                             ==> b₂₇[x₁₇] == b₂₄[x₁₇]))
                                                    && (forall i₁₅: int ::
                                                          (  i₁₅ <= i₁₅
                                                            && 0 <= i₁₅
                                                            && i₁₅ < i₂₈
                                                             ==> i₁₅ < N))
                                                     ==> (i₂₈ < N
                                                         ==> true
                                                          && 0 <= i₂₈ + 1
                                                          && i₂₈ + 1 <= N
                                                          && (forall x₁₆: int ::
                                                                ((exists i₁₅: int ::
                                                                        x₁₆ == i₁₅
                                                                        && 0 <= i₁₅
                                                                        && i₁₅ < i₂₈ + 1)
                                                                   ==> (exists i₁₅: int ::
                                                                          i₁₅ < N
                                                                          && x₁₆ == i₁₅
                                                                          && 0 <= i₁₅
                                                                          && i₁₅ < i₂₈ + 1
                                                                          && a₂₆[i₂₈ := -b₂₇[i₂₈]][x₁₆] == -b₂₄[i₁₅])))
                                                          && (forall x₁₆: int ::
                                                                (!((exists i₁₅: int ::
                                                                        x₁₆ == i₁₅
                                                                        && 0 <= i₁₅
                                                                        && i₁₅ < i₂₈ + 1)
                                                                )
                                                                   ==> a₂₆[i₂₈ := -b₂₇[i₂₈]][x₁₆] == a₂₃[x₁₆]))
                                                          && (forall x₁₇: int ::
                                                                ((exists i₁₅: int ::
                                                                        x₁₇ == i₁₅
                                                                        && 0 <= i₁₅
                                                                        && i₁₅ < i₂₈ + 1)
                                                                   ==> (exists i₁₅: int ::
                                                                          i₁₅ < N
                                                                          && x₁₇ == i₁₅
                                                                          && 0 <= i₁₅
                                                                          && i₁₅ < i₂₈ + 1
                                                                          && b₂₇[i₂₈ := a₂₆[i₂₈]][x₁₇] == a₂₃[i₁₅])))
                                                          && (forall x₁₇: int ::
                                                                (!((exists i₁₅: int ::
                                                                        x₁₇ == i₁₅
                                                                        && 0 <= i₁₅
                                                                        && i₁₅ < i₂₈ + 1)
                                                                )
                                                                   ==> b₂₇[i₂₈ := a₂₆[i₂₈]][x₁₇] == b₂₄[x₁₇]))
                                                          && (forall i₁₅: int ::
                                                                (  i₁₅ <= i₁₅
                                                                  && 0 <= i₁₅
                                                                  && i₁₅ < i₂₈ + 1
                                                                   ==> i₁₅ < N))
                                                          && true
                                                          && (true
                                                             ==> true))
                                                      && (!(i₂₈ < N
                                                      )
                                                         ==> true
                                                          && (true
                                                             ==> true
                                                              && 1 <= 1
                                                              && 1 <= N
                                                              && (forall i₂₁: int ::
                                                                    (  i₂₁ <= i₂₁
                                                                      && 1 <= i₂₁
                                                                      && i₂₁ < 1
                                                                       ==> i₂₁ < N))
                                                              && (forall i₂₉: int ::
                                                                    (  true
                                                                      && 1 <= i₂₉
                                                                      && i₂₉ <= N
                                                                      && (forall i₂₁: int ::
                                                                            (  i₂₁ <= i₂₁
                                                                              && 1 <= i₂₁
                                                                              && i₂₁ < i₂₉
                                                                               ==> i₂₁ < N))
                                                                       ==> (i₂₉ < N
                                                                           ==> a₂₆[i₂₉] == b₂₇[i₂₉]
                                                                            && (true
                                                                               ==> true
                                                                                && 1 <= i₂₉ + 1
                                                                                && i₂₉ + 1 <= N
                                                                                && (forall i₂₁: int ::
                                                                                      (  i₂₁ <= i₂₁
                                                                                        && 1 <= i₂₁
                                                                                        && i₂₁ < i₂₉ + 1
                                                                                         ==> i₂₁ < N))
                                                                                && true
                                                                                && (true
                                                                                   ==> true)))
                                                                        && (!(i₂₉ < N
                                                                        )
                                                                           ==> true
                                                                            && (true
                                                                               ==> true)))))))))))))))));


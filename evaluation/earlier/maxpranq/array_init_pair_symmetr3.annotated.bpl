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
                                && (  N < 100000
                                  && 0 < N
                                   ==> true
                                    && 1 <= 1
                                    && 1 <= N
                                    && (forall x₁₁: int ::
                                          ((exists i₁₀: int ::
                                                  x₁₁ == i₁₀
                                                  && 1 <= i₁₀
                                                  && i₁₀ < 1)
                                             ==> (exists x₉: int, i₁₀: int ::
                                                    x₉ < 100000
                                                    && -100000 < x₉
                                                    && i₁₀ < N
                                                    && x₁₁ == i₁₀
                                                    && 1 <= i₁₀
                                                    && i₁₀ < 1
                                                    && a[x₁₁] == x₉ + N)))
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
                                             ==> (exists x₉: int, i₁₀: int ::
                                                    x₉ < 100000
                                                    && -100000 < x₉
                                                    && i₁₀ < N
                                                    && x₁₂ == i₁₀
                                                    && 1 <= i₁₀
                                                    && i₁₀ < 1
                                                    && b[x₁₂] == x₉)))
                                    && (forall x₁₂: int ::
                                          (!((exists i₁₀: int ::
                                                  x₁₂ == i₁₀
                                                  && 1 <= i₁₀
                                                  && i₁₀ < 1)
                                          )
                                             ==> b[x₁₂] == b[x₁₂]))
                                    && (forall i₁₀: int ::
                                          (  i₁₀ <= i₁₀
                                            && 1 <= i₁₀
                                            && i₁₀ < 1
                                             ==> i₁₀ < N))
                                    && (forall a₂₂: [int]int, b₂₃: [int]int, i₂₄: int ::
                                          (  true
                                            && 1 <= i₂₄
                                            && i₂₄ <= N
                                            && (forall x₁₁: int ::
                                                  ((exists i₁₀: int ::
                                                          x₁₁ == i₁₀
                                                          && 1 <= i₁₀
                                                          && i₁₀ < i₂₄)
                                                     ==> (exists x₉: int, i₁₀: int ::
                                                            x₉ < 100000
                                                            && -100000 < x₉
                                                            && i₁₀ < N
                                                            && x₁₁ == i₁₀
                                                            && 1 <= i₁₀
                                                            && i₁₀ < i₂₄
                                                            && a₂₂[x₁₁] == x₉ + N)))
                                            && (forall x₁₁: int ::
                                                  (!((exists i₁₀: int ::
                                                          x₁₁ == i₁₀
                                                          && 1 <= i₁₀
                                                          && i₁₀ < i₂₄)
                                                  )
                                                     ==> a₂₂[x₁₁] == a[x₁₁]))
                                            && (forall x₁₂: int ::
                                                  ((exists i₁₀: int ::
                                                          x₁₂ == i₁₀
                                                          && 1 <= i₁₀
                                                          && i₁₀ < i₂₄)
                                                     ==> (exists x₉: int, i₁₀: int ::
                                                            x₉ < 100000
                                                            && -100000 < x₉
                                                            && i₁₀ < N
                                                            && x₁₂ == i₁₀
                                                            && 1 <= i₁₀
                                                            && i₁₀ < i₂₄
                                                            && b₂₃[x₁₂] == x₉)))
                                            && (forall x₁₂: int ::
                                                  (!((exists i₁₀: int ::
                                                          x₁₂ == i₁₀
                                                          && 1 <= i₁₀
                                                          && i₁₀ < i₂₄)
                                                  )
                                                     ==> b₂₃[x₁₂] == b[x₁₂]))
                                            && (forall i₁₀: int ::
                                                  (  i₁₀ <= i₁₀
                                                    && 1 <= i₁₀
                                                    && i₁₀ < i₂₄
                                                     ==> i₁₀ < N))
                                             ==> (i₂₄ < N
                                                 ==> (forall x: int ::
                                                        true
                                                        && (  x < 100000
                                                          && -100000 < x
                                                           ==> true
                                                            && 1 <= i₂₄ + 1
                                                            && i₂₄ + 1 <= N
                                                            && (forall x₁₁: int ::
                                                                  ((exists i₁₀: int ::
                                                                          x₁₁ == i₁₀
                                                                          && 1 <= i₁₀
                                                                          && i₁₀ < i₂₄ + 1)
                                                                     ==> (exists x₉: int, i₁₀: int ::
                                                                            x₉ < 100000
                                                                            && -100000 < x₉
                                                                            && i₁₀ < N
                                                                            && x₁₁ == i₁₀
                                                                            && 1 <= i₁₀
                                                                            && i₁₀ < i₂₄ + 1
                                                                            && a₂₂[i₂₄ := N + x][x₁₁] == x₉ + N)))
                                                            && (forall x₁₁: int ::
                                                                  (!((exists i₁₀: int ::
                                                                          x₁₁ == i₁₀
                                                                          && 1 <= i₁₀
                                                                          && i₁₀ < i₂₄ + 1)
                                                                  )
                                                                     ==> a₂₂[i₂₄ := N + x][x₁₁] == a[x₁₁]))
                                                            && (forall x₁₂: int ::
                                                                  ((exists i₁₀: int ::
                                                                          x₁₂ == i₁₀
                                                                          && 1 <= i₁₀
                                                                          && i₁₀ < i₂₄ + 1)
                                                                     ==> (exists x₉: int, i₁₀: int ::
                                                                            x₉ < 100000
                                                                            && -100000 < x₉
                                                                            && i₁₀ < N
                                                                            && x₁₂ == i₁₀
                                                                            && 1 <= i₁₀
                                                                            && i₁₀ < i₂₄ + 1
                                                                            && b₂₃[i₂₄ := x][x₁₂] == x₉)))
                                                            && (forall x₁₂: int ::
                                                                  (!((exists i₁₀: int ::
                                                                          x₁₂ == i₁₀
                                                                          && 1 <= i₁₀
                                                                          && i₁₀ < i₂₄ + 1)
                                                                  )
                                                                     ==> b₂₃[i₂₄ := x][x₁₂] == b[x₁₂]))
                                                            && (forall i₁₀: int ::
                                                                  (  i₁₀ <= i₁₀
                                                                    && 1 <= i₁₀
                                                                    && i₁₀ < i₂₄ + 1
                                                                     ==> i₁₀ < N))
                                                            && true
                                                            && (true
                                                               ==> true))))
                                              && (!(i₂₄ < N
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
                                                                      && c[x₁₇] == a₂₂[i₁₆] + -b₂₃[i₁₆])))
                                                      && (forall x₁₇: int ::
                                                            (!((exists i₁₆: int ::
                                                                    x₁₇ == i₁₆
                                                                    && 0 <= i₁₆
                                                                    && i₁₆ < 0)
                                                            )
                                                               ==> c[x₁₇] == c[x₁₇]))
                                                      && (forall i₁₆: int ::
                                                            (  i₁₆ <= i₁₆
                                                              && 0 <= i₁₆
                                                              && i₁₆ < 0
                                                               ==> i₁₆ < N))
                                                      && (forall c₂₅: [int]int, i₂₆: int ::
                                                            (  true
                                                              && 0 <= i₂₆
                                                              && i₂₆ <= N
                                                              && (forall x₁₇: int ::
                                                                    ((exists i₁₆: int ::
                                                                            x₁₇ == i₁₆
                                                                            && 0 <= i₁₆
                                                                            && i₁₆ < i₂₆)
                                                                       ==> (exists i₁₆: int ::
                                                                              i₁₆ < N
                                                                              && x₁₇ == i₁₆
                                                                              && 0 <= i₁₆
                                                                              && i₁₆ < i₂₆
                                                                              && c₂₅[x₁₇] == a₂₂[i₁₆] + -b₂₃[i₁₆])))
                                                              && (forall x₁₇: int ::
                                                                    (!((exists i₁₆: int ::
                                                                            x₁₇ == i₁₆
                                                                            && 0 <= i₁₆
                                                                            && i₁₆ < i₂₆)
                                                                    )
                                                                       ==> c₂₅[x₁₇] == c[x₁₇]))
                                                              && (forall i₁₆: int ::
                                                                    (  i₁₆ <= i₁₆
                                                                      && 0 <= i₁₆
                                                                      && i₁₆ < i₂₆
                                                                       ==> i₁₆ < N))
                                                               ==> (i₂₆ < N
                                                                   ==> true
                                                                    && 0 <= i₂₆ + 1
                                                                    && i₂₆ + 1 <= N
                                                                    && (forall x₁₇: int ::
                                                                          ((exists i₁₆: int ::
                                                                                  x₁₇ == i₁₆
                                                                                  && 0 <= i₁₆
                                                                                  && i₁₆ < i₂₆ + 1)
                                                                             ==> (exists i₁₆: int ::
                                                                                    i₁₆ < N
                                                                                    && x₁₇ == i₁₆
                                                                                    && 0 <= i₁₆
                                                                                    && i₁₆ < i₂₆ + 1
                                                                                    && c₂₅[i₂₆ := a₂₂[i₂₆] - b₂₃[i₂₆]][x₁₇] == a₂₂[i₁₆] + -b₂₃[i₁₆])))
                                                                    && (forall x₁₇: int ::
                                                                          (!((exists i₁₆: int ::
                                                                                  x₁₇ == i₁₆
                                                                                  && 0 <= i₁₆
                                                                                  && i₁₆ < i₂₆ + 1)
                                                                          )
                                                                             ==> c₂₅[i₂₆ := a₂₂[i₂₆] - b₂₃[i₂₆]][x₁₇] == c[x₁₇]))
                                                                    && (forall i₁₆: int ::
                                                                          (  i₁₆ <= i₁₆
                                                                            && 0 <= i₁₆
                                                                            && i₁₆ < i₂₆ + 1
                                                                             ==> i₁₆ < N))
                                                                    && true
                                                                    && (true
                                                                       ==> true))
                                                                && (!(i₂₆ < N
                                                                )
                                                                   ==> true
                                                                    && (true
                                                                       ==> true
                                                                        && 1 <= 1
                                                                        && 1 <= N
                                                                        && (forall i₂₀: int ::
                                                                              (  i₂₀ <= i₂₀
                                                                                && 1 <= i₂₀
                                                                                && i₂₀ < 1
                                                                                 ==> i₂₀ < N))
                                                                        && (forall i₂₇: int ::
                                                                              (  true
                                                                                && 1 <= i₂₇
                                                                                && i₂₇ <= N
                                                                                && (forall i₂₀: int ::
                                                                                      (  i₂₀ <= i₂₀
                                                                                        && 1 <= i₂₀
                                                                                        && i₂₀ < i₂₇
                                                                                         ==> i₂₀ < N))
                                                                                 ==> (i₂₇ < N
                                                                                     ==> c₂₅[i₂₇] == N
                                                                                      && (true
                                                                                         ==> true
                                                                                          && 1 <= i₂₇ + 1
                                                                                          && i₂₇ + 1 <= N
                                                                                          && (forall i₂₀: int ::
                                                                                                (  i₂₀ <= i₂₀
                                                                                                  && 1 <= i₂₀
                                                                                                  && i₂₀ < i₂₇ + 1
                                                                                                   ==> i₂₀ < N))
                                                                                          && true
                                                                                          && (true
                                                                                             ==> true)))
                                                                                  && (!(i₂₇ < N
                                                                                  )
                                                                                     ==> true
                                                                                      && (true
                                                                                         ==> true)))))))))))))))))));


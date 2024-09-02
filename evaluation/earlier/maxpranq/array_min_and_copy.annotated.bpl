data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> (forall j: int ::
        (forall N: int ::
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
                                         ==> (exists k₉: int, i₁₀: int ::
                                                j <= k₉
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
                                && (forall i₁₀: int ::
                                      (  1 <= i₁₀
                                        && i₁₀ < 1
                                         ==> i₁₀ < N))
                                && (forall a₂₀: [int]int, i₂₁: int ::
                                      (  true
                                        && 1 <= i₂₁
                                        && i₂₁ <= N
                                        && (forall x₁₁: int ::
                                              ((exists i₁₀: int ::
                                                      x₁₁ == i₁₀
                                                      && 1 <= i₁₀
                                                      && i₁₀ < i₂₁)
                                                 ==> (exists k₉: int, i₁₀: int ::
                                                        j <= k₉
                                                        && i₁₀ < N
                                                        && x₁₁ == i₁₀
                                                        && 1 <= i₁₀
                                                        && i₁₀ < i₂₁
                                                        && a₂₀[x₁₁] == k₉)))
                                        && (forall x₁₁: int ::
                                              (!((exists i₁₀: int ::
                                                      x₁₁ == i₁₀
                                                      && 1 <= i₁₀
                                                      && i₁₀ < i₂₁)
                                              )
                                                 ==> a₂₀[x₁₁] == a[x₁₁]))
                                        && (forall i₁₀: int ::
                                              (  1 <= i₁₀
                                                && i₁₀ < i₂₁
                                                 ==> i₁₀ < N))
                                         ==> (i₂₁ < N
                                             ==> (forall k: int ::
                                                    true
                                                    && (j <= k
                                                       ==> true
                                                        && 1 <= i₂₁ + 1
                                                        && i₂₁ + 1 <= N
                                                        && (forall x₁₁: int ::
                                                              ((exists i₁₀: int ::
                                                                      x₁₁ == i₁₀
                                                                      && 1 <= i₁₀
                                                                      && i₁₀ < i₂₁ + 1)
                                                                 ==> (exists k₉: int, i₁₀: int ::
                                                                        j <= k₉
                                                                        && i₁₀ < N
                                                                        && x₁₁ == i₁₀
                                                                        && 1 <= i₁₀
                                                                        && i₁₀ < i₂₁ + 1
                                                                        && a₂₀[i₂₁ := k][x₁₁] == k₉)))
                                                        && (forall x₁₁: int ::
                                                              (!((exists i₁₀: int ::
                                                                      x₁₁ == i₁₀
                                                                      && 1 <= i₁₀
                                                                      && i₁₀ < i₂₁ + 1)
                                                              )
                                                                 ==> a₂₀[i₂₁ := k][x₁₁] == a[x₁₁]))
                                                        && (forall i₁₀: int ::
                                                              (  1 <= i₁₀
                                                                && i₁₀ < i₂₁ + 1
                                                                 ==> i₁₀ < N))
                                                        && true
                                                        && (true
                                                           ==> true))))
                                          && (!(i₂₁ < N
                                          )
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= N
                                                  && (forall x₁₅: int ::
                                                        ((exists i₁₄: int ::
                                                                x₁₅ == i₁₄
                                                                && 0 <= i₁₄
                                                                && i₁₄ < 0)
                                                           ==> (exists i₁₄: int ::
                                                                  i₁₄ < N
                                                                  && x₁₅ == i₁₄
                                                                  && 0 <= i₁₄
                                                                  && i₁₄ < 0
                                                                  && b[x₁₅] == a₂₀[i₁₄])))
                                                  && (forall x₁₅: int ::
                                                        (!((exists i₁₄: int ::
                                                                x₁₅ == i₁₄
                                                                && 0 <= i₁₄
                                                                && i₁₄ < 0)
                                                        )
                                                           ==> b[x₁₅] == b[x₁₅]))
                                                  && (forall i₁₄: int ::
                                                        (  0 <= i₁₄
                                                          && i₁₄ < 0
                                                           ==> i₁₄ < N))
                                                  && (forall b₂₂: [int]int, i₂₃: int ::
                                                        (  true
                                                          && 0 <= i₂₃
                                                          && i₂₃ <= N
                                                          && (forall x₁₅: int ::
                                                                ((exists i₁₄: int ::
                                                                        x₁₅ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₂₃)
                                                                   ==> (exists i₁₄: int ::
                                                                          i₁₄ < N
                                                                          && x₁₅ == i₁₄
                                                                          && 0 <= i₁₄
                                                                          && i₁₄ < i₂₃
                                                                          && b₂₂[x₁₅] == a₂₀[i₁₄])))
                                                          && (forall x₁₅: int ::
                                                                (!((exists i₁₄: int ::
                                                                        x₁₅ == i₁₄
                                                                        && 0 <= i₁₄
                                                                        && i₁₄ < i₂₃)
                                                                )
                                                                   ==> b₂₂[x₁₅] == b[x₁₅]))
                                                          && (forall i₁₄: int ::
                                                                (  0 <= i₁₄
                                                                  && i₁₄ < i₂₃
                                                                   ==> i₁₄ < N))
                                                           ==> (i₂₃ < N
                                                               ==> true
                                                                && 0 <= i₂₃ + 1
                                                                && i₂₃ + 1 <= N
                                                                && (forall x₁₅: int ::
                                                                      ((exists i₁₄: int ::
                                                                              x₁₅ == i₁₄
                                                                              && 0 <= i₁₄
                                                                              && i₁₄ < i₂₃ + 1)
                                                                         ==> (exists i₁₄: int ::
                                                                                i₁₄ < N
                                                                                && x₁₅ == i₁₄
                                                                                && 0 <= i₁₄
                                                                                && i₁₄ < i₂₃ + 1
                                                                                && b₂₂[i₂₃ := a₂₀[i₂₃]][x₁₅] == a₂₀[i₁₄])))
                                                                && (forall x₁₅: int ::
                                                                      (!((exists i₁₄: int ::
                                                                              x₁₅ == i₁₄
                                                                              && 0 <= i₁₄
                                                                              && i₁₄ < i₂₃ + 1)
                                                                      )
                                                                         ==> b₂₂[i₂₃ := a₂₀[i₂₃]][x₁₅] == b[x₁₅]))
                                                                && (forall i₁₄: int ::
                                                                      (  0 <= i₁₄
                                                                        && i₁₄ < i₂₃ + 1
                                                                         ==> i₁₄ < N))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (!(i₂₃ < N
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true
                                                                    && 1 <= 1
                                                                    && 1 <= N
                                                                    && (forall i₁₈: int ::
                                                                          (  1 <= i₁₈
                                                                            && i₁₈ < 1
                                                                             ==> i₁₈ < N))
                                                                    && (forall i₂₄: int ::
                                                                          (  true
                                                                            && 1 <= i₂₄
                                                                            && i₂₄ <= N
                                                                            && (forall i₁₈: int ::
                                                                                  (  1 <= i₁₈
                                                                                    && i₁₈ < i₂₄
                                                                                     ==> i₁₈ < N))
                                                                             ==> (i₂₄ < N
                                                                                 ==> j <= b₂₂[i₂₄]
                                                                                  && (true
                                                                                     ==> true
                                                                                      && 1 <= i₂₄ + 1
                                                                                      && i₂₄ + 1 <= N
                                                                                      && (forall i₁₈: int ::
                                                                                            (  1 <= i₁₈
                                                                                              && i₁₈ < i₂₄ + 1
                                                                                               ==> i₁₈ < N))
                                                                                      && true
                                                                                      && (true
                                                                                         ==> true)))
                                                                              && (!(i₂₄ < N
                                                                              )
                                                                                 ==> true
                                                                                  && (true
                                                                                     ==> true))))))))))))))))));


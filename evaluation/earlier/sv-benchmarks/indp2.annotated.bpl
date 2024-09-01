data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall N₁₈: int ::
          (true
             ==> (N₁₈ <= 0
                 ==> true)
              && (!(N₁₈ <= 0
              )
                 ==> true
                  && (N₁₈ <= 2147483647 / 4
                     ==> (forall a: [int]int ::
                            true
                            && 0 <= 0
                            && 0 <= N₁₈
                            && (forall x₅: int ::
                                  ((exists i₄: int ::
                                          x₅ == i₄
                                          && 0 <= i₄
                                          && i₄ < 0)
                                     ==> (exists i₄: int ::
                                            i₄ < N₁₈
                                            && x₅ == i₄
                                            && 0 <= i₄
                                            && i₄ < 0
                                            && a[x₅] == -1 + i₄ * i₄)))
                            && (forall x₅: int ::
                                  (!((exists i₄: int ::
                                          x₅ == i₄
                                          && 0 <= i₄
                                          && i₄ < 0)
                                  )
                                     ==> a[x₅] == a[x₅]))
                            && (forall i₄: int ::
                                  (  i₄ <= i₄
                                    && 0 <= i₄
                                    && i₄ < 0
                                     ==> i₄ < N₁₈))
                            && (forall a₁₉: [int]int, i₂₀: int ::
                                  (  true
                                    && 0 <= i₂₀
                                    && i₂₀ <= N₁₈
                                    && (forall x₅: int ::
                                          ((exists i₄: int ::
                                                  x₅ == i₄
                                                  && 0 <= i₄
                                                  && i₄ < i₂₀)
                                             ==> (exists i₄: int ::
                                                    i₄ < N₁₈
                                                    && x₅ == i₄
                                                    && 0 <= i₄
                                                    && i₄ < i₂₀
                                                    && a₁₉[x₅] == -1 + i₄ * i₄)))
                                    && (forall x₅: int ::
                                          (!((exists i₄: int ::
                                                  x₅ == i₄
                                                  && 0 <= i₄
                                                  && i₄ < i₂₀)
                                          )
                                             ==> a₁₉[x₅] == a[x₅]))
                                    && (forall i₄: int ::
                                          (  i₄ <= i₄
                                            && 0 <= i₄
                                            && i₄ < i₂₀
                                             ==> i₄ < N₁₈))
                                     ==> (i₂₀ < N₁₈
                                         ==> true
                                          && 0 <= i₂₀ + 1
                                          && i₂₀ + 1 <= N₁₈
                                          && (forall x₅: int ::
                                                ((exists i₄: int ::
                                                        x₅ == i₄
                                                        && 0 <= i₄
                                                        && i₄ < i₂₀ + 1)
                                                   ==> (exists i₄: int ::
                                                          i₄ < N₁₈
                                                          && x₅ == i₄
                                                          && 0 <= i₄
                                                          && i₄ < i₂₀ + 1
                                                          && a₁₉[i₂₀ := (i₂₀ - 1) * (i₂₀ + 1)][x₅] == -1 + i₄ * i₄)))
                                          && (forall x₅: int ::
                                                (!((exists i₄: int ::
                                                        x₅ == i₄
                                                        && 0 <= i₄
                                                        && i₄ < i₂₀ + 1)
                                                )
                                                   ==> a₁₉[i₂₀ := (i₂₀ - 1) * (i₂₀ + 1)][x₅] == a[x₅]))
                                          && (forall i₄: int ::
                                                (  i₄ <= i₄
                                                  && 0 <= i₄
                                                  && i₄ < i₂₀ + 1
                                                   ==> i₄ < N₁₈))
                                          && true
                                          && (true
                                             ==> true))
                                      && (!(i₂₀ < N₁₈
                                      )
                                         ==> true
                                          && (true
                                             ==> true
                                              && 0 <= 0
                                              && 0 <= N₁₈
                                              && (forall x₉: int ::
                                                    ((exists i₈: int ::
                                                            x₉ == i₈
                                                            && 0 <= i₈
                                                            && i₈ < 0)
                                                       ==> (exists i₈: int ::
                                                              i₈ < N₁₈
                                                              && x₉ == i₈
                                                              && 0 <= i₈
                                                              && i₈ < 0
                                                              && a₁₉[x₉] == -(i₈ * i₈) + a₁₉[i₈])))
                                              && (forall x₉: int ::
                                                    (!((exists i₈: int ::
                                                            x₉ == i₈
                                                            && 0 <= i₈
                                                            && i₈ < 0)
                                                    )
                                                       ==> a₁₉[x₉] == a₁₉[x₉]))
                                              && (forall i₈: int ::
                                                    (  i₈ <= i₈
                                                      && 0 <= i₈
                                                      && i₈ < 0
                                                       ==> i₈ < N₁₈))
                                              && (forall a₂₁: [int]int, i₂₂: int ::
                                                    (  true
                                                      && 0 <= i₂₂
                                                      && i₂₂ <= N₁₈
                                                      && (forall x₉: int ::
                                                            ((exists i₈: int ::
                                                                    x₉ == i₈
                                                                    && 0 <= i₈
                                                                    && i₈ < i₂₂)
                                                               ==> (exists i₈: int ::
                                                                      i₈ < N₁₈
                                                                      && x₉ == i₈
                                                                      && 0 <= i₈
                                                                      && i₈ < i₂₂
                                                                      && a₂₁[x₉] == -(i₈ * i₈) + a₁₉[i₈])))
                                                      && (forall x₉: int ::
                                                            (!((exists i₈: int ::
                                                                    x₉ == i₈
                                                                    && 0 <= i₈
                                                                    && i₈ < i₂₂)
                                                            )
                                                               ==> a₂₁[x₉] == a₁₉[x₉]))
                                                      && (forall i₈: int ::
                                                            (  i₈ <= i₈
                                                              && 0 <= i₈
                                                              && i₈ < i₂₂
                                                               ==> i₈ < N₁₈))
                                                       ==> (i₂₂ < N₁₈
                                                           ==> true
                                                            && 0 <= i₂₂ + 1
                                                            && i₂₂ + 1 <= N₁₈
                                                            && (forall x₉: int ::
                                                                  ((exists i₈: int ::
                                                                          x₉ == i₈
                                                                          && 0 <= i₈
                                                                          && i₈ < i₂₂ + 1)
                                                                     ==> (exists i₈: int ::
                                                                            i₈ < N₁₈
                                                                            && x₉ == i₈
                                                                            && 0 <= i₈
                                                                            && i₈ < i₂₂ + 1
                                                                            && a₂₁[i₂₂ := a₂₁[i₂₂] - i₂₂ * i₂₂][x₉] == -(i₈ * i₈) + a₁₉[i₈])))
                                                            && (forall x₉: int ::
                                                                  (!((exists i₈: int ::
                                                                          x₉ == i₈
                                                                          && 0 <= i₈
                                                                          && i₈ < i₂₂ + 1)
                                                                  )
                                                                     ==> a₂₁[i₂₂ := a₂₁[i₂₂] - i₂₂ * i₂₂][x₉] == a₁₉[x₉]))
                                                            && (forall i₈: int ::
                                                                  (  i₈ <= i₈
                                                                    && 0 <= i₈
                                                                    && i₈ < i₂₂ + 1
                                                                     ==> i₈ < N₁₈))
                                                            && true
                                                            && (true
                                                               ==> true))
                                                        && (!(i₂₂ < N₁₈
                                                        )
                                                           ==> true
                                                            && (true
                                                               ==> true
                                                                && 0 <= 0
                                                                && 0 <= N₁₈
                                                                && (forall x₁₃: int ::
                                                                      ((exists i₁₂: int ::
                                                                              x₁₃ == i₁₂
                                                                              && 0 <= i₁₂
                                                                              && i₁₂ < 0)
                                                                         ==> (exists i₁₂: int ::
                                                                                i₁₂ < N₁₈
                                                                                && x₁₃ == i₁₂
                                                                                && 0 <= i₁₂
                                                                                && i₁₂ < 0
                                                                                && a₂₁[x₁₃] == 1 + a₂₁[i₁₂])))
                                                                && (forall x₁₃: int ::
                                                                      (!((exists i₁₂: int ::
                                                                              x₁₃ == i₁₂
                                                                              && 0 <= i₁₂
                                                                              && i₁₂ < 0)
                                                                      )
                                                                         ==> a₂₁[x₁₃] == a₂₁[x₁₃]))
                                                                && (forall i₁₂: int ::
                                                                      (  i₁₂ <= i₁₂
                                                                        && 0 <= i₁₂
                                                                        && i₁₂ < 0
                                                                         ==> i₁₂ < N₁₈))
                                                                && (forall a₂₃: [int]int, i₂₄: int ::
                                                                      (  true
                                                                        && 0 <= i₂₄
                                                                        && i₂₄ <= N₁₈
                                                                        && (forall x₁₃: int ::
                                                                              ((exists i₁₂: int ::
                                                                                      x₁₃ == i₁₂
                                                                                      && 0 <= i₁₂
                                                                                      && i₁₂ < i₂₄)
                                                                                 ==> (exists i₁₂: int ::
                                                                                        i₁₂ < N₁₈
                                                                                        && x₁₃ == i₁₂
                                                                                        && 0 <= i₁₂
                                                                                        && i₁₂ < i₂₄
                                                                                        && a₂₃[x₁₃] == 1 + a₂₁[i₁₂])))
                                                                        && (forall x₁₃: int ::
                                                                              (!((exists i₁₂: int ::
                                                                                      x₁₃ == i₁₂
                                                                                      && 0 <= i₁₂
                                                                                      && i₁₂ < i₂₄)
                                                                              )
                                                                                 ==> a₂₃[x₁₃] == a₂₁[x₁₃]))
                                                                        && (forall i₁₂: int ::
                                                                              (  i₁₂ <= i₁₂
                                                                                && 0 <= i₁₂
                                                                                && i₁₂ < i₂₄
                                                                                 ==> i₁₂ < N₁₈))
                                                                         ==> (i₂₄ < N₁₈
                                                                             ==> true
                                                                              && 0 <= i₂₄ + 1
                                                                              && i₂₄ + 1 <= N₁₈
                                                                              && (forall x₁₃: int ::
                                                                                    ((exists i₁₂: int ::
                                                                                            x₁₃ == i₁₂
                                                                                            && 0 <= i₁₂
                                                                                            && i₁₂ < i₂₄ + 1)
                                                                                       ==> (exists i₁₂: int ::
                                                                                              i₁₂ < N₁₈
                                                                                              && x₁₃ == i₁₂
                                                                                              && 0 <= i₁₂
                                                                                              && i₁₂ < i₂₄ + 1
                                                                                              && a₂₃[i₂₄ := a₂₃[i₂₄] + 1][x₁₃] == 1 + a₂₁[i₁₂])))
                                                                              && (forall x₁₃: int ::
                                                                                    (!((exists i₁₂: int ::
                                                                                            x₁₃ == i₁₂
                                                                                            && 0 <= i₁₂
                                                                                            && i₁₂ < i₂₄ + 1)
                                                                                    )
                                                                                       ==> a₂₃[i₂₄ := a₂₃[i₂₄] + 1][x₁₃] == a₂₁[x₁₃]))
                                                                              && (forall i₁₂: int ::
                                                                                    (  i₁₂ <= i₁₂
                                                                                      && 0 <= i₁₂
                                                                                      && i₁₂ < i₂₄ + 1
                                                                                       ==> i₁₂ < N₁₈))
                                                                              && true
                                                                              && (true
                                                                                 ==> true))
                                                                          && (!(i₂₄ < N₁₈
                                                                          )
                                                                             ==> true
                                                                              && (true
                                                                                 ==> true
                                                                                  && 0 <= 0
                                                                                  && 0 <= N₁₈
                                                                                  && (forall i₁₆: int ::
                                                                                        (  i₁₆ <= i₁₆
                                                                                          && 0 <= i₁₆
                                                                                          && i₁₆ < 0
                                                                                           ==> i₁₆ < N₁₈))
                                                                                  && (forall i₂₅: int ::
                                                                                        (  true
                                                                                          && 0 <= i₂₅
                                                                                          && i₂₅ <= N₁₈
                                                                                          && (forall i₁₆: int ::
                                                                                                (  i₁₆ <= i₁₆
                                                                                                  && 0 <= i₁₆
                                                                                                  && i₁₆ < i₂₅
                                                                                                   ==> i₁₆ < N₁₈))
                                                                                           ==> (i₂₅ < N₁₈
                                                                                               ==> a₂₃[i₂₅] == 0
                                                                                                && (true
                                                                                                   ==> true
                                                                                                    && 0 <= i₂₅ + 1
                                                                                                    && i₂₅ + 1 <= N₁₈
                                                                                                    && (forall i₁₆: int ::
                                                                                                          (  i₁₆ <= i₁₆
                                                                                                            && 0 <= i₁₆
                                                                                                            && i₁₆ < i₂₅ + 1
                                                                                                             ==> i₁₆ < N₁₈))
                                                                                                    && true
                                                                                                    && (true
                                                                                                       ==> true)))
                                                                                            && (!(i₂₅ < N₁₈
                                                                                            )
                                                                                               ==> true
                                                                                                && (true
                                                                                                   ==> true))))))))))))))))))))));


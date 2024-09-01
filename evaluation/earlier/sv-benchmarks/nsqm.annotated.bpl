data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall N₁₅: int ::
          (true
             ==> (N₁₅ <= 0
                 ==> true)
              && (!(N₁₅ <= 0
              )
                 ==> true
                  && (N₁₅ <= 2147483647 / 4
                     ==> (forall a: [int]int ::
                          (forall b: [int]int ::
                                  true
                                  && 1 <= 1
                                  && 1 <= N₁₅
                                  && (forall x₆: int ::
                                        ((exists i₅: int ::
                                                x₆ == i₅
                                                && 1 <= i₅
                                                && i₅ < 1)
                                           ==> (exists i₅: int ::
                                                  i₅ < N₁₅
                                                  && x₆ == i₅
                                                  && 1 <= i₅
                                                  && i₅ < 1
                                                  && b[0 := 1][x₆] == 2 + b[0 := 1][-1 + i₅])))
                                  && (forall x₆: int ::
                                        (!((exists i₅: int ::
                                                x₆ == i₅
                                                && 1 <= i₅
                                                && i₅ < 1)
                                        )
                                           ==> b[0 := 1][x₆] == b[0 := 1][x₆]))
                                  && (forall i₅: int ::
                                        (  i₅ <= i₅
                                          && 1 <= i₅
                                          && i₅ < 1
                                           ==> i₅ < N₁₅))
                                  && (forall b₁₆: [int]int, i₁₇: int ::
                                        (  true
                                          && 1 <= i₁₇
                                          && i₁₇ <= N₁₅
                                          && (forall x₆: int ::
                                                ((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 1 <= i₅
                                                        && i₅ < i₁₇)
                                                   ==> (exists i₅: int ::
                                                          i₅ < N₁₅
                                                          && x₆ == i₅
                                                          && 1 <= i₅
                                                          && i₅ < i₁₇
                                                          && b₁₆[x₆] == 2 + b[0 := 1][-1 + i₅])))
                                          && (forall x₆: int ::
                                                (!((exists i₅: int ::
                                                        x₆ == i₅
                                                        && 1 <= i₅
                                                        && i₅ < i₁₇)
                                                )
                                                   ==> b₁₆[x₆] == b[0 := 1][x₆]))
                                          && (forall i₅: int ::
                                                (  i₅ <= i₅
                                                  && 1 <= i₅
                                                  && i₅ < i₁₇
                                                   ==> i₅ < N₁₅))
                                           ==> (i₁₇ < N₁₅
                                               ==> true
                                                && 1 <= i₁₇ + 1
                                                && i₁₇ + 1 <= N₁₅
                                                && (forall x₆: int ::
                                                      ((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 1 <= i₅
                                                              && i₅ < i₁₇ + 1)
                                                         ==> (exists i₅: int ::
                                                                i₅ < N₁₅
                                                                && x₆ == i₅
                                                                && 1 <= i₅
                                                                && i₅ < i₁₇ + 1
                                                                && b₁₆[i₁₇ := b₁₆[i₁₇ - 1] + 2][x₆] == 2 + b[0 := 1][-1 + i₅])))
                                                && (forall x₆: int ::
                                                      (!((exists i₅: int ::
                                                              x₆ == i₅
                                                              && 1 <= i₅
                                                              && i₅ < i₁₇ + 1)
                                                      )
                                                         ==> b₁₆[i₁₇ := b₁₆[i₁₇ - 1] + 2][x₆] == b[0 := 1][x₆]))
                                                && (forall i₅: int ::
                                                      (  i₅ <= i₅
                                                        && 1 <= i₅
                                                        && i₅ < i₁₇ + 1
                                                         ==> i₅ < N₁₅))
                                                && true
                                                && (true
                                                   ==> true))
                                            && (!(i₁₇ < N₁₅
                                            )
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 1 <= 1
                                                    && 1 <= N₁₅
                                                    && (forall x₁₀: int ::
                                                          ((exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 1 <= i₉
                                                                  && i₉ < 1)
                                                             ==> (exists i₉: int ::
                                                                    i₉ < N₁₅
                                                                    && x₁₀ == i₉
                                                                    && 1 <= i₉
                                                                    && i₉ < 1
                                                                    && a[0 := N₁₅ + 1][x₁₀] == 2 + b₁₆[-1 + i₉] + a[0 := N₁₅ + 1][-1 + i₉])))
                                                    && (forall x₁₀: int ::
                                                          (!((exists i₉: int ::
                                                                  x₁₀ == i₉
                                                                  && 1 <= i₉
                                                                  && i₉ < 1)
                                                          )
                                                             ==> a[0 := N₁₅ + 1][x₁₀] == a[0 := N₁₅ + 1][x₁₀]))
                                                    && (forall i₉: int ::
                                                          (  i₉ <= i₉
                                                            && 1 <= i₉
                                                            && i₉ < 1
                                                             ==> i₉ < N₁₅))
                                                    && (forall a₁₈: [int]int, i₁₉: int ::
                                                          (  true
                                                            && 1 <= i₁₉
                                                            && i₁₉ <= N₁₅
                                                            && (forall x₁₀: int ::
                                                                  ((exists i₉: int ::
                                                                          x₁₀ == i₉
                                                                          && 1 <= i₉
                                                                          && i₉ < i₁₉)
                                                                     ==> (exists i₉: int ::
                                                                            i₉ < N₁₅
                                                                            && x₁₀ == i₉
                                                                            && 1 <= i₉
                                                                            && i₉ < i₁₉
                                                                            && a₁₈[x₁₀] == 2 + b₁₆[-1 + i₉] + a[0 := N₁₅ + 1][-1 + i₉])))
                                                            && (forall x₁₀: int ::
                                                                  (!((exists i₉: int ::
                                                                          x₁₀ == i₉
                                                                          && 1 <= i₉
                                                                          && i₉ < i₁₉)
                                                                  )
                                                                     ==> a₁₈[x₁₀] == a[0 := N₁₅ + 1][x₁₀]))
                                                            && (forall i₉: int ::
                                                                  (  i₉ <= i₉
                                                                    && 1 <= i₉
                                                                    && i₉ < i₁₉
                                                                     ==> i₉ < N₁₅))
                                                             ==> (i₁₉ < N₁₅
                                                                 ==> true
                                                                  && 1 <= i₁₉ + 1
                                                                  && i₁₉ + 1 <= N₁₅
                                                                  && (forall x₁₀: int ::
                                                                        ((exists i₉: int ::
                                                                                x₁₀ == i₉
                                                                                && 1 <= i₉
                                                                                && i₉ < i₁₉ + 1)
                                                                           ==> (exists i₉: int ::
                                                                                  i₉ < N₁₅
                                                                                  && x₁₀ == i₉
                                                                                  && 1 <= i₉
                                                                                  && i₉ < i₁₉ + 1
                                                                                  && a₁₈[i₁₉ := a₁₈[i₁₉ - 1] + b₁₆[i₁₉ - 1] + 2][x₁₀] == 2 + b₁₆[-1 + i₉] + a[0 := N₁₅ + 1][-1 + i₉])))
                                                                  && (forall x₁₀: int ::
                                                                        (!((exists i₉: int ::
                                                                                x₁₀ == i₉
                                                                                && 1 <= i₉
                                                                                && i₉ < i₁₉ + 1)
                                                                        )
                                                                           ==> a₁₈[i₁₉ := a₁₈[i₁₉ - 1] + b₁₆[i₁₉ - 1] + 2][x₁₀] == a[0 := N₁₅ + 1][x₁₀]))
                                                                  && (forall i₉: int ::
                                                                        (  i₉ <= i₉
                                                                          && 1 <= i₉
                                                                          && i₉ < i₁₉ + 1
                                                                           ==> i₉ < N₁₅))
                                                                  && true
                                                                  && (true
                                                                     ==> true))
                                                              && (!(i₁₉ < N₁₅
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> true
                                                                      && 0 <= 0
                                                                      && 0 <= N₁₅
                                                                      && (forall i₁₃: int ::
                                                                            (  i₁₃ <= i₁₃
                                                                              && 0 <= i₁₃
                                                                              && i₁₃ < 0
                                                                               ==> i₁₃ < N₁₅))
                                                                      && (forall i₂₀: int ::
                                                                            (  true
                                                                              && 0 <= i₂₀
                                                                              && i₂₀ <= N₁₅
                                                                              && (forall i₁₃: int ::
                                                                                    (  i₁₃ <= i₁₃
                                                                                      && 0 <= i₁₃
                                                                                      && i₁₃ < i₂₀
                                                                                       ==> i₁₃ < N₁₅))
                                                                               ==> (i₂₀ < N₁₅
                                                                                   ==> a₁₈[i₂₀] == N₁₅ + (i₂₀ + 1) * (i₂₀ + 1)
                                                                                    && (true
                                                                                       ==> true
                                                                                        && 0 <= i₂₀ + 1
                                                                                        && i₂₀ + 1 <= N₁₅
                                                                                        && (forall i₁₃: int ::
                                                                                              (  i₁₃ <= i₁₃
                                                                                                && 0 <= i₁₃
                                                                                                && i₁₃ < i₂₀ + 1
                                                                                                 ==> i₁₃ < N₁₅))
                                                                                        && true
                                                                                        && (true
                                                                                           ==> true)))
                                                                                && (!(i₂₀ < N₁₅
                                                                                )
                                                                                   ==> true
                                                                                    && (true
                                                                                       ==> true)))))))))))))))))));


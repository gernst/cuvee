data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall N₁₄: int ::
          (true
             ==> (N₁₄ <= 0
                 ==> true)
              && (!(N₁₄ <= 0
              )
                 ==> true
                  && (N₁₄ <= 2147483647 / 4
                     ==> (forall a: [int]int ::
                            true
                            && 0 <= 0
                            && 0 <= N₁₄
                            && (forall x₅: int ::
                                  ((exists i₄: int ::
                                          x₅ == i₄
                                          && 0 <= i₄
                                          && i₄ < 0)
                                     ==> (exists i₄: int ::
                                            i₄ < N₁₄
                                            && x₅ == i₄
                                            && 0 <= i₄
                                            && i₄ < 0
                                            && a[x₅] == 0)))
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
                                     ==> i₄ < N₁₄))
                            && (forall a₁₅: [int]int, i₁₆: int ::
                                  (  true
                                    && 0 <= i₁₆
                                    && i₁₆ <= N₁₄
                                    && (forall x₅: int ::
                                          ((exists i₄: int ::
                                                  x₅ == i₄
                                                  && 0 <= i₄
                                                  && i₄ < i₁₆)
                                             ==> (exists i₄: int ::
                                                    i₄ < N₁₄
                                                    && x₅ == i₄
                                                    && 0 <= i₄
                                                    && i₄ < i₁₆
                                                    && a₁₅[x₅] == 0)))
                                    && (forall x₅: int ::
                                          (!((exists i₄: int ::
                                                  x₅ == i₄
                                                  && 0 <= i₄
                                                  && i₄ < i₁₆)
                                          )
                                             ==> a₁₅[x₅] == a[x₅]))
                                    && (forall i₄: int ::
                                          (  i₄ <= i₄
                                            && 0 <= i₄
                                            && i₄ < i₁₆
                                             ==> i₄ < N₁₄))
                                     ==> (i₁₆ < N₁₄
                                         ==> true
                                          && 0 <= i₁₆ + 1
                                          && i₁₆ + 1 <= N₁₄
                                          && (forall x₅: int ::
                                                ((exists i₄: int ::
                                                        x₅ == i₄
                                                        && 0 <= i₄
                                                        && i₄ < i₁₆ + 1)
                                                   ==> (exists i₄: int ::
                                                          i₄ < N₁₄
                                                          && x₅ == i₄
                                                          && 0 <= i₄
                                                          && i₄ < i₁₆ + 1
                                                          && a₁₅[i₁₆ := 0][x₅] == 0)))
                                          && (forall x₅: int ::
                                                (!((exists i₄: int ::
                                                        x₅ == i₄
                                                        && 0 <= i₄
                                                        && i₄ < i₁₆ + 1)
                                                )
                                                   ==> a₁₅[i₁₆ := 0][x₅] == a[x₅]))
                                          && (forall i₄: int ::
                                                (  i₄ <= i₄
                                                  && 0 <= i₄
                                                  && i₄ < i₁₆ + 1
                                                   ==> i₄ < N₁₄))
                                          && true
                                          && (true
                                             ==> true))
                                      && (!(i₁₆ < N₁₄
                                      )
                                         ==> true
                                          && (true
                                             ==> true
                                              && 0 <= 0
                                              && 0 <= N₁₄
                                              && (forall x₉: int ::
                                                    ((exists i₈: int ::
                                                            x₉ == i₈
                                                            && 0 <= i₈
                                                            && i₈ < 0)
                                                       ==> (exists i₈: int ::
                                                                N₁₄ % 2 == 0
                                                                && i₈ < N₁₄
                                                                && x₉ == i₈
                                                                && 0 <= i₈
                                                                && i₈ < 0
                                                                && a₁₅[x₉] == 2 + a₁₅[i₈])
                                                        || (exists i₈: int ::
                                                                N₁₄ % 2 != 0
                                                                && i₈ < N₁₄
                                                                && x₉ == i₈
                                                                && 0 <= i₈
                                                                && i₈ < 0
                                                                && a₁₅[x₉] == 1 + a₁₅[i₈])))
                                              && (forall x₉: int ::
                                                    (!((exists i₈: int ::
                                                            x₉ == i₈
                                                            && 0 <= i₈
                                                            && i₈ < 0)
                                                    )
                                                       ==> a₁₅[x₉] == a₁₅[x₉]))
                                              && (forall i₈: int ::
                                                    (  i₈ <= i₈
                                                      && 0 <= i₈
                                                      && i₈ < 0
                                                       ==> i₈ < N₁₄))
                                              && (forall a₁₇: [int]int, i₁₈: int ::
                                                    (  true
                                                      && 0 <= i₁₈
                                                      && i₁₈ <= N₁₄
                                                      && (forall x₉: int ::
                                                            ((exists i₈: int ::
                                                                    x₉ == i₈
                                                                    && 0 <= i₈
                                                                    && i₈ < i₁₈)
                                                               ==> (exists i₈: int ::
                                                                        N₁₄ % 2 == 0
                                                                        && i₈ < N₁₄
                                                                        && x₉ == i₈
                                                                        && 0 <= i₈
                                                                        && i₈ < i₁₈
                                                                        && a₁₇[x₉] == 2 + a₁₅[i₈])
                                                                || (exists i₈: int ::
                                                                        N₁₄ % 2 != 0
                                                                        && i₈ < N₁₄
                                                                        && x₉ == i₈
                                                                        && 0 <= i₈
                                                                        && i₈ < i₁₈
                                                                        && a₁₇[x₉] == 1 + a₁₅[i₈])))
                                                      && (forall x₉: int ::
                                                            (!((exists i₈: int ::
                                                                    x₉ == i₈
                                                                    && 0 <= i₈
                                                                    && i₈ < i₁₈)
                                                            )
                                                               ==> a₁₇[x₉] == a₁₅[x₉]))
                                                      && (forall i₈: int ::
                                                            (  i₈ <= i₈
                                                              && 0 <= i₈
                                                              && i₈ < i₁₈
                                                               ==> i₈ < N₁₄))
                                                       ==> (i₁₈ < N₁₄
                                                           ==> (N₁₄ % 2 == 0
                                                               ==> true
                                                                && 0 <= i₁₈ + 1
                                                                && i₁₈ + 1 <= N₁₄
                                                                && (forall x₉: int ::
                                                                      ((exists i₈: int ::
                                                                              x₉ == i₈
                                                                              && 0 <= i₈
                                                                              && i₈ < i₁₈ + 1)
                                                                         ==> (exists i₈: int ::
                                                                                  N₁₄ % 2 == 0
                                                                                  && i₈ < N₁₄
                                                                                  && x₉ == i₈
                                                                                  && 0 <= i₈
                                                                                  && i₈ < i₁₈ + 1
                                                                                  && a₁₇[i₁₈ := a₁₇[i₁₈] + 2][x₉] == 2 + a₁₅[i₈])
                                                                          || (exists i₈: int ::
                                                                                  N₁₄ % 2 != 0
                                                                                  && i₈ < N₁₄
                                                                                  && x₉ == i₈
                                                                                  && 0 <= i₈
                                                                                  && i₈ < i₁₈ + 1
                                                                                  && a₁₇[i₁₈ := a₁₇[i₁₈] + 2][x₉] == 1 + a₁₅[i₈])))
                                                                && (forall x₉: int ::
                                                                      (!((exists i₈: int ::
                                                                              x₉ == i₈
                                                                              && 0 <= i₈
                                                                              && i₈ < i₁₈ + 1)
                                                                      )
                                                                         ==> a₁₇[i₁₈ := a₁₇[i₁₈] + 2][x₉] == a₁₅[x₉]))
                                                                && (forall i₈: int ::
                                                                      (  i₈ <= i₈
                                                                        && 0 <= i₈
                                                                        && i₈ < i₁₈ + 1
                                                                         ==> i₈ < N₁₄))
                                                                && true
                                                                && (true
                                                                   ==> true))
                                                            && (N₁₄ % 2 != 0
                                                               ==> true
                                                                && 0 <= i₁₈ + 1
                                                                && i₁₈ + 1 <= N₁₄
                                                                && (forall x₉: int ::
                                                                      ((exists i₈: int ::
                                                                              x₉ == i₈
                                                                              && 0 <= i₈
                                                                              && i₈ < i₁₈ + 1)
                                                                         ==> (exists i₈: int ::
                                                                                  N₁₄ % 2 == 0
                                                                                  && i₈ < N₁₄
                                                                                  && x₉ == i₈
                                                                                  && 0 <= i₈
                                                                                  && i₈ < i₁₈ + 1
                                                                                  && a₁₇[i₁₈ := a₁₇[i₁₈] + 1][x₉] == 2 + a₁₅[i₈])
                                                                          || (exists i₈: int ::
                                                                                  N₁₄ % 2 != 0
                                                                                  && i₈ < N₁₄
                                                                                  && x₉ == i₈
                                                                                  && 0 <= i₈
                                                                                  && i₈ < i₁₈ + 1
                                                                                  && a₁₇[i₁₈ := a₁₇[i₁₈] + 1][x₉] == 1 + a₁₅[i₈])))
                                                                && (forall x₉: int ::
                                                                      (!((exists i₈: int ::
                                                                              x₉ == i₈
                                                                              && 0 <= i₈
                                                                              && i₈ < i₁₈ + 1)
                                                                      )
                                                                         ==> a₁₇[i₁₈ := a₁₇[i₁₈] + 1][x₉] == a₁₅[x₉]))
                                                                && (forall i₈: int ::
                                                                      (  i₈ <= i₈
                                                                        && 0 <= i₈
                                                                        && i₈ < i₁₈ + 1
                                                                         ==> i₈ < N₁₄))
                                                                && true
                                                                && (true
                                                                   ==> true)))
                                                        && (!(i₁₈ < N₁₄
                                                        )
                                                           ==> true
                                                            && (true
                                                               ==> true
                                                                && 0 <= 0
                                                                && 0 <= N₁₄
                                                                && (forall i₁₂: int ::
                                                                      (  i₁₂ <= i₁₂
                                                                        && 0 <= i₁₂
                                                                        && i₁₂ < 0
                                                                         ==> i₁₂ < N₁₄))
                                                                && (forall i₁₉: int ::
                                                                      (  true
                                                                        && 0 <= i₁₉
                                                                        && i₁₉ <= N₁₄
                                                                        && (forall i₁₂: int ::
                                                                              (  i₁₂ <= i₁₂
                                                                                && 0 <= i₁₂
                                                                                && i₁₂ < i₁₉
                                                                                 ==> i₁₂ < N₁₄))
                                                                         ==> (i₁₉ < N₁₄
                                                                             ==> a₁₇[i₁₉] % 2 == N₁₄ % 2
                                                                              && (true
                                                                                 ==> true
                                                                                  && 0 <= i₁₉ + 1
                                                                                  && i₁₉ + 1 <= N₁₄
                                                                                  && (forall i₁₂: int ::
                                                                                        (  i₁₂ <= i₁₂
                                                                                          && 0 <= i₁₂
                                                                                          && i₁₂ < i₁₉ + 1
                                                                                           ==> i₁₂ < N₁₄))
                                                                                  && true
                                                                                  && (true
                                                                                     ==> true)))
                                                                          && (!(i₁₉ < N₁₄
                                                                          )
                                                                             ==> true
                                                                              && (true
                                                                                 ==> true))))))))))))))))));


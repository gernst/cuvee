data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int, N: int ::
      (true
         ==> true
          && 0 <= 0
          && 0 <= N
          && (forall i₅: int ::
                (  i₅ <= i₅
                  && 0 <= i₅
                  && i₅ < 0
                   ==> i₅ < N))
          && (forall ret₂₇: int, i₂₈: int ::
                (  true
                  && 0 <= i₂₈
                  && i₂₈ <= N
                  && (forall i₅: int ::
                        (  i₅ <= i₅
                          && 0 <= i₅
                          && i₅ < i₂₈
                           ==> i₅ < N))
                   ==> (i₂₈ < N
                       ==> (ret₂₇ < x[i₂₈]
                           ==> true
                            && 0 <= i₂₈ + 1
                            && i₂₈ + 1 <= N
                            && (forall i₅: int ::
                                  (  i₅ <= i₅
                                    && 0 <= i₅
                                    && i₅ < i₂₈ + 1
                                     ==> i₅ < N))
                            && true
                            && (true
                               ==> true))
                        && (!(ret₂₇ < x[i₂₈]
                        )
                           ==> true
                            && 0 <= i₂₈ + 1
                            && i₂₈ + 1 <= N
                            && (forall i₅: int ::
                                  (  i₅ <= i₅
                                    && 0 <= i₅
                                    && i₅ < i₂₈ + 1
                                     ==> i₅ < N))
                            && true
                            && (true
                               ==> true)))
                    && (!(i₂₈ < N
                    )
                       ==> true
                        && (true
                           ==> true))))));

goal (true
   ==> true
    && (forall N₃₃: int ::
          (true
             ==> (1 < N₃₃
                 ==> (forall x: [int]int ::
                        true
                        && (true
                           ==> true
                            && 0 <= 0
                            && 0 <= N₃₃
                            && (forall i₅: int ::
                                  (  i₅ <= i₅
                                    && 0 <= i₅
                                    && i₅ < 0
                                     ==> i₅ < N₃₃))
                            && (forall ret₃₇: int, i₃₈: int ::
                                  (  true
                                    && 0 <= i₃₈
                                    && i₃₈ <= N₃₃
                                    && (forall i₅: int ::
                                          (  i₅ <= i₅
                                            && 0 <= i₅
                                            && i₅ < i₃₈
                                             ==> i₅ < N₃₃))
                                     ==> (i₃₈ < N₃₃
                                         ==> (ret₃₇ < x[i₃₈]
                                             ==> true
                                              && 0 <= i₃₈ + 1
                                              && i₃₈ + 1 <= N₃₃
                                              && (forall i₅: int ::
                                                    (  i₅ <= i₅
                                                      && 0 <= i₅
                                                      && i₅ < i₃₈ + 1
                                                       ==> i₅ < N₃₃))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (!(ret₃₇ < x[i₃₈]
                                          )
                                             ==> true
                                              && 0 <= i₃₈ + 1
                                              && i₃₈ + 1 <= N₃₃
                                              && (forall i₅: int ::
                                                    (  i₅ <= i₅
                                                      && 0 <= i₅
                                                      && i₅ < i₃₈ + 1
                                                       ==> i₅ < N₃₃))
                                              && true
                                              && (true
                                                 ==> true)))
                                      && (!(i₃₈ < N₃₃
                                      )
                                         ==> true
                                          && (true
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= N₃₃
                                                  && (forall i₅: int ::
                                                        (  i₅ <= i₅
                                                          && 0 <= i₅
                                                          && i₅ < 0
                                                           ==> i₅ < N₃₃))
                                                  && (forall ret₄₃: int, i₄₄: int ::
                                                        (  true
                                                          && 0 <= i₄₄
                                                          && i₄₄ <= N₃₃
                                                          && (forall i₅: int ::
                                                                (  i₅ <= i₅
                                                                  && 0 <= i₅
                                                                  && i₅ < i₄₄
                                                                   ==> i₅ < N₃₃))
                                                           ==> (i₄₄ < N₃₃
                                                               ==> (ret₄₃ < x[0 := x[1]][1 := x[0]][i₄₄]
                                                                   ==> true
                                                                    && 0 <= i₄₄ + 1
                                                                    && i₄₄ + 1 <= N₃₃
                                                                    && (forall i₅: int ::
                                                                          (  i₅ <= i₅
                                                                            && 0 <= i₅
                                                                            && i₅ < i₄₄ + 1
                                                                             ==> i₅ < N₃₃))
                                                                    && true
                                                                    && (true
                                                                       ==> true))
                                                                && (!(ret₄₃ < x[0 := x[1]][1 := x[0]][i₄₄]
                                                                )
                                                                   ==> true
                                                                    && 0 <= i₄₄ + 1
                                                                    && i₄₄ + 1 <= N₃₃
                                                                    && (forall i₅: int ::
                                                                          (  i₅ <= i₅
                                                                            && 0 <= i₅
                                                                            && i₅ < i₄₄ + 1
                                                                             ==> i₅ < N₃₃))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(i₄₄ < N₃₃
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= 0
                                                                    && 0 <= -1 + N₃₃
                                                                    && (forall x₂₁: int ::
                                                                          ((exists i₂₀: int ::
                                                                                  x₂₁ == i₂₀
                                                                                  && 0 <= i₂₀
                                                                                  && i₂₀ < 0)
                                                                             ==> (exists i₂₀: int ::
                                                                                    i₂₀ < -1 + N₃₃
                                                                                    && x₂₁ == i₂₀
                                                                                    && 0 <= i₂₀
                                                                                    && i₂₀ < 0
                                                                                    && x[0 := x[1]][1 := x[0]][x₂₁] == x[0 := x[1]][1 := x[0]][1 + i₂₀])))
                                                                    && (forall x₂₁: int ::
                                                                          (!((exists i₂₀: int ::
                                                                                  x₂₁ == i₂₀
                                                                                  && 0 <= i₂₀
                                                                                  && i₂₀ < 0)
                                                                          )
                                                                             ==> x[0 := x[1]][1 := x[0]][x₂₁] == x[0 := x[1]][1 := x[0]][x₂₁]))
                                                                    && (forall i₂₀: int ::
                                                                          (  i₂₀ <= i₂₀
                                                                            && 0 <= i₂₀
                                                                            && i₂₀ < 0
                                                                             ==> i₂₀ < -1 + N₃₃))
                                                                    && (forall x₄₆: [int]int, i₄₇: int ::
                                                                          (  true
                                                                            && 0 <= i₄₇
                                                                            && i₄₇ <= -1 + N₃₃
                                                                            && (forall x₂₁: int ::
                                                                                  ((exists i₂₀: int ::
                                                                                          x₂₁ == i₂₀
                                                                                          && 0 <= i₂₀
                                                                                          && i₂₀ < i₄₇)
                                                                                     ==> (exists i₂₀: int ::
                                                                                            i₂₀ < -1 + N₃₃
                                                                                            && x₂₁ == i₂₀
                                                                                            && 0 <= i₂₀
                                                                                            && i₂₀ < i₄₇
                                                                                            && x₄₆[x₂₁] == x[0 := x[1]][1 := x[0]][1 + i₂₀])))
                                                                            && (forall x₂₁: int ::
                                                                                  (!((exists i₂₀: int ::
                                                                                          x₂₁ == i₂₀
                                                                                          && 0 <= i₂₀
                                                                                          && i₂₀ < i₄₇)
                                                                                  )
                                                                                     ==> x₄₆[x₂₁] == x[0 := x[1]][1 := x[0]][x₂₁]))
                                                                            && (forall i₂₀: int ::
                                                                                  (  i₂₀ <= i₂₀
                                                                                    && 0 <= i₂₀
                                                                                    && i₂₀ < i₄₇
                                                                                     ==> i₂₀ < -1 + N₃₃))
                                                                             ==> (i₄₇ < N₃₃ - 1
                                                                                 ==> true
                                                                                  && 0 <= i₄₇ + 1
                                                                                  && i₄₇ + 1 <= -1 + N₃₃
                                                                                  && (forall x₂₁: int ::
                                                                                        ((exists i₂₀: int ::
                                                                                                x₂₁ == i₂₀
                                                                                                && 0 <= i₂₀
                                                                                                && i₂₀ < i₄₇ + 1)
                                                                                           ==> (exists i₂₀: int ::
                                                                                                  i₂₀ < -1 + N₃₃
                                                                                                  && x₂₁ == i₂₀
                                                                                                  && 0 <= i₂₀
                                                                                                  && i₂₀ < i₄₇ + 1
                                                                                                  && x₄₆[i₄₇ := x₄₆[i₄₇ + 1]][x₂₁] == x[0 := x[1]][1 := x[0]][1 + i₂₀])))
                                                                                  && (forall x₂₁: int ::
                                                                                        (!((exists i₂₀: int ::
                                                                                                x₂₁ == i₂₀
                                                                                                && 0 <= i₂₀
                                                                                                && i₂₀ < i₄₇ + 1)
                                                                                        )
                                                                                           ==> x₄₆[i₄₇ := x₄₆[i₄₇ + 1]][x₂₁] == x[0 := x[1]][1 := x[0]][x₂₁]))
                                                                                  && (forall i₂₀: int ::
                                                                                        (  i₂₀ <= i₂₀
                                                                                          && 0 <= i₂₀
                                                                                          && i₂₀ < i₄₇ + 1
                                                                                           ==> i₂₀ < -1 + N₃₃))
                                                                                  && true
                                                                                  && (true
                                                                                     ==> true))
                                                                              && (!(i₄₇ < N₃₃ - 1
                                                                              )
                                                                                 ==> true
                                                                                  && (true
                                                                                     ==> true
                                                                                      && (true
                                                                                         ==> true
                                                                                          && 0 <= 0
                                                                                          && 0 <= N₃₃
                                                                                          && (forall i₅: int ::
                                                                                                (  i₅ <= i₅
                                                                                                  && 0 <= i₅
                                                                                                  && i₅ < 0
                                                                                                   ==> i₅ < N₃₃))
                                                                                          && (forall ret₅₂: int, i₅₃: int ::
                                                                                                (  true
                                                                                                  && 0 <= i₅₃
                                                                                                  && i₅₃ <= N₃₃
                                                                                                  && (forall i₅: int ::
                                                                                                        (  i₅ <= i₅
                                                                                                          && 0 <= i₅
                                                                                                          && i₅ < i₅₃
                                                                                                           ==> i₅ < N₃₃))
                                                                                                   ==> (i₅₃ < N₃₃
                                                                                                       ==> (ret₅₂ < x₄₆[N₃₃ - 1 := x[0 := x[1]][1 := x[0]][0]][i₅₃]
                                                                                                           ==> true
                                                                                                            && 0 <= i₅₃ + 1
                                                                                                            && i₅₃ + 1 <= N₃₃
                                                                                                            && (forall i₅: int ::
                                                                                                                  (  i₅ <= i₅
                                                                                                                    && 0 <= i₅
                                                                                                                    && i₅ < i₅₃ + 1
                                                                                                                     ==> i₅ < N₃₃))
                                                                                                            && true
                                                                                                            && (true
                                                                                                               ==> true))
                                                                                                        && (!(ret₅₂ < x₄₆[N₃₃ - 1 := x[0 := x[1]][1 := x[0]][0]][i₅₃]
                                                                                                        )
                                                                                                           ==> true
                                                                                                            && 0 <= i₅₃ + 1
                                                                                                            && i₅₃ + 1 <= N₃₃
                                                                                                            && (forall i₅: int ::
                                                                                                                  (  i₅ <= i₅
                                                                                                                    && 0 <= i₅
                                                                                                                    && i₅ < i₅₃ + 1
                                                                                                                     ==> i₅ < N₃₃))
                                                                                                            && true
                                                                                                            && (true
                                                                                                               ==> true)))
                                                                                                    && (!(i₅₃ < N₃₃
                                                                                                    )
                                                                                                       ==> true
                                                                                                        && (true
                                                                                                           ==> (  ret₃₇ != ret₄₃
                                                                                                              || ret₃₇ != ret₅₂
                                                                                                               ==> false
                                                                                                                && (true
                                                                                                                   ==> true))
                                                                                                            && (!(  ret₃₇ != ret₄₃
                                                                                                              || ret₃₇ != ret₅₂
                                                                                                            )
                                                                                                               ==> true))))))))))))))))))))))
              && (!(1 < N₃₃
              )
                 ==> true))));


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
          && (forall i₂: int ::
                (  i₂ <= i₂
                  && 0 <= i₂
                  && i₂ < 0
                   ==> i₂ < N))
          && (forall i₂₅: int ::
                (  true
                  && 0 <= i₂₅
                  && i₂₅ <= N
                  && (forall i₂: int ::
                        (  i₂ <= i₂
                          && 0 <= i₂
                          && i₂ < i₂₅
                           ==> i₂ < N))
                   ==> (i₂₅ < N
                       ==> (x[i₂₅] % 2 == 0
                           ==> true
                            && 0 <= i₂₅ + 1
                            && i₂₅ + 1 <= N
                            && (forall i₂: int ::
                                  (  i₂ <= i₂
                                    && 0 <= i₂
                                    && i₂ < i₂₅ + 1
                                     ==> i₂ < N))
                            && true
                            && (true
                               ==> true))
                        && (x[i₂₅] % 2 != 0
                           ==> true
                            && 0 <= i₂₅ + 1
                            && i₂₅ + 1 <= N
                            && (forall i₂: int ::
                                  (  i₂ <= i₂
                                    && 0 <= i₂
                                    && i₂ < i₂₅ + 1
                                     ==> i₂ < N))
                            && true
                            && (true
                               ==> true)))
                    && (!(i₂₅ < N
                    )
                       ==> true
                        && (true
                           ==> true))))));

goal (true
   ==> true
    && (forall N₃₀: int ::
          (true
             ==> (1 < N₃₀
                 ==> (forall x: [int]int ::
                        true
                        && (true
                           ==> true
                            && 0 <= 0
                            && 0 <= N₃₀
                            && (forall i₂: int ::
                                  (  i₂ <= i₂
                                    && 0 <= i₂
                                    && i₂ < 0
                                     ==> i₂ < N₃₀))
                            && (forall ret₃₄: int, i₃₅: int ::
                                  (  true
                                    && 0 <= i₃₅
                                    && i₃₅ <= N₃₀
                                    && (forall i₂: int ::
                                          (  i₂ <= i₂
                                            && 0 <= i₂
                                            && i₂ < i₃₅
                                             ==> i₂ < N₃₀))
                                     ==> (i₃₅ < N₃₀
                                         ==> (x[i₃₅] % 2 == 0
                                             ==> true
                                              && 0 <= i₃₅ + 1
                                              && i₃₅ + 1 <= N₃₀
                                              && (forall i₂: int ::
                                                    (  i₂ <= i₂
                                                      && 0 <= i₂
                                                      && i₂ < i₃₅ + 1
                                                       ==> i₂ < N₃₀))
                                              && true
                                              && (true
                                                 ==> true))
                                          && (x[i₃₅] % 2 != 0
                                             ==> true
                                              && 0 <= i₃₅ + 1
                                              && i₃₅ + 1 <= N₃₀
                                              && (forall i₂: int ::
                                                    (  i₂ <= i₂
                                                      && 0 <= i₂
                                                      && i₂ < i₃₅ + 1
                                                       ==> i₂ < N₃₀))
                                              && true
                                              && (true
                                                 ==> true)))
                                      && (!(i₃₅ < N₃₀
                                      )
                                         ==> true
                                          && (true
                                             ==> true
                                              && (true
                                                 ==> true
                                                  && 0 <= 0
                                                  && 0 <= N₃₀
                                                  && (forall i₂: int ::
                                                        (  i₂ <= i₂
                                                          && 0 <= i₂
                                                          && i₂ < 0
                                                           ==> i₂ < N₃₀))
                                                  && (forall ret₄₀: int, i₄₁: int ::
                                                        (  true
                                                          && 0 <= i₄₁
                                                          && i₄₁ <= N₃₀
                                                          && (forall i₂: int ::
                                                                (  i₂ <= i₂
                                                                  && 0 <= i₂
                                                                  && i₂ < i₄₁
                                                                   ==> i₂ < N₃₀))
                                                           ==> (i₄₁ < N₃₀
                                                               ==> (x[0 := x[1]][1 := x[0]][i₄₁] % 2 == 0
                                                                   ==> true
                                                                    && 0 <= i₄₁ + 1
                                                                    && i₄₁ + 1 <= N₃₀
                                                                    && (forall i₂: int ::
                                                                          (  i₂ <= i₂
                                                                            && 0 <= i₂
                                                                            && i₂ < i₄₁ + 1
                                                                             ==> i₂ < N₃₀))
                                                                    && true
                                                                    && (true
                                                                       ==> true))
                                                                && (x[0 := x[1]][1 := x[0]][i₄₁] % 2 != 0
                                                                   ==> true
                                                                    && 0 <= i₄₁ + 1
                                                                    && i₄₁ + 1 <= N₃₀
                                                                    && (forall i₂: int ::
                                                                          (  i₂ <= i₂
                                                                            && 0 <= i₂
                                                                            && i₂ < i₄₁ + 1
                                                                             ==> i₂ < N₃₀))
                                                                    && true
                                                                    && (true
                                                                       ==> true)))
                                                            && (!(i₄₁ < N₃₀
                                                            )
                                                               ==> true
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= 0
                                                                    && 0 <= -1 + N₃₀
                                                                    && (forall x₁₈: int ::
                                                                          ((exists i₁₇: int ::
                                                                                  x₁₈ == i₁₇
                                                                                  && 0 <= i₁₇
                                                                                  && i₁₇ < 0)
                                                                             ==> (exists i₁₇: int ::
                                                                                    i₁₇ < -1 + N₃₀
                                                                                    && x₁₈ == i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < 0
                                                                                    && x[0 := x[1]][1 := x[0]][x₁₈] == x[0 := x[1]][1 := x[0]][1 + i₁₇])))
                                                                    && (forall x₁₈: int ::
                                                                          (!((exists i₁₇: int ::
                                                                                  x₁₈ == i₁₇
                                                                                  && 0 <= i₁₇
                                                                                  && i₁₇ < 0)
                                                                          )
                                                                             ==> x[0 := x[1]][1 := x[0]][x₁₈] == x[0 := x[1]][1 := x[0]][x₁₈]))
                                                                    && (forall i₁₇: int ::
                                                                          (  i₁₇ <= i₁₇
                                                                            && 0 <= i₁₇
                                                                            && i₁₇ < 0
                                                                             ==> i₁₇ < -1 + N₃₀))
                                                                    && (forall x₄₃: [int]int, i₄₄: int ::
                                                                          (  true
                                                                            && 0 <= i₄₄
                                                                            && i₄₄ <= -1 + N₃₀
                                                                            && (forall x₁₈: int ::
                                                                                  ((exists i₁₇: int ::
                                                                                          x₁₈ == i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₄₄)
                                                                                     ==> (exists i₁₇: int ::
                                                                                            i₁₇ < -1 + N₃₀
                                                                                            && x₁₈ == i₁₇
                                                                                            && 0 <= i₁₇
                                                                                            && i₁₇ < i₄₄
                                                                                            && x₄₃[x₁₈] == x[0 := x[1]][1 := x[0]][1 + i₁₇])))
                                                                            && (forall x₁₈: int ::
                                                                                  (!((exists i₁₇: int ::
                                                                                          x₁₈ == i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₄₄)
                                                                                  )
                                                                                     ==> x₄₃[x₁₈] == x[0 := x[1]][1 := x[0]][x₁₈]))
                                                                            && (forall i₁₇: int ::
                                                                                  (  i₁₇ <= i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < i₄₄
                                                                                     ==> i₁₇ < -1 + N₃₀))
                                                                             ==> (i₄₄ < N₃₀ - 1
                                                                                 ==> true
                                                                                  && 0 <= i₄₄ + 1
                                                                                  && i₄₄ + 1 <= -1 + N₃₀
                                                                                  && (forall x₁₈: int ::
                                                                                        ((exists i₁₇: int ::
                                                                                                x₁₈ == i₁₇
                                                                                                && 0 <= i₁₇
                                                                                                && i₁₇ < i₄₄ + 1)
                                                                                           ==> (exists i₁₇: int ::
                                                                                                  i₁₇ < -1 + N₃₀
                                                                                                  && x₁₈ == i₁₇
                                                                                                  && 0 <= i₁₇
                                                                                                  && i₁₇ < i₄₄ + 1
                                                                                                  && x₄₃[i₄₄ := x₄₃[i₄₄ + 1]][x₁₈] == x[0 := x[1]][1 := x[0]][1 + i₁₇])))
                                                                                  && (forall x₁₈: int ::
                                                                                        (!((exists i₁₇: int ::
                                                                                                x₁₈ == i₁₇
                                                                                                && 0 <= i₁₇
                                                                                                && i₁₇ < i₄₄ + 1)
                                                                                        )
                                                                                           ==> x₄₃[i₄₄ := x₄₃[i₄₄ + 1]][x₁₈] == x[0 := x[1]][1 := x[0]][x₁₈]))
                                                                                  && (forall i₁₇: int ::
                                                                                        (  i₁₇ <= i₁₇
                                                                                          && 0 <= i₁₇
                                                                                          && i₁₇ < i₄₄ + 1
                                                                                           ==> i₁₇ < -1 + N₃₀))
                                                                                  && true
                                                                                  && (true
                                                                                     ==> true))
                                                                              && (!(i₄₄ < N₃₀ - 1
                                                                              )
                                                                                 ==> true
                                                                                  && (true
                                                                                     ==> true
                                                                                      && (true
                                                                                         ==> true
                                                                                          && 0 <= 0
                                                                                          && 0 <= N₃₀
                                                                                          && (forall i₂: int ::
                                                                                                (  i₂ <= i₂
                                                                                                  && 0 <= i₂
                                                                                                  && i₂ < 0
                                                                                                   ==> i₂ < N₃₀))
                                                                                          && (forall ret₄₉: int, i₅₀: int ::
                                                                                                (  true
                                                                                                  && 0 <= i₅₀
                                                                                                  && i₅₀ <= N₃₀
                                                                                                  && (forall i₂: int ::
                                                                                                        (  i₂ <= i₂
                                                                                                          && 0 <= i₂
                                                                                                          && i₂ < i₅₀
                                                                                                           ==> i₂ < N₃₀))
                                                                                                   ==> (i₅₀ < N₃₀
                                                                                                       ==> (x₄₃[N₃₀ - 1 := x[0 := x[1]][1 := x[0]][0]][i₅₀] % 2 == 0
                                                                                                           ==> true
                                                                                                            && 0 <= i₅₀ + 1
                                                                                                            && i₅₀ + 1 <= N₃₀
                                                                                                            && (forall i₂: int ::
                                                                                                                  (  i₂ <= i₂
                                                                                                                    && 0 <= i₂
                                                                                                                    && i₂ < i₅₀ + 1
                                                                                                                     ==> i₂ < N₃₀))
                                                                                                            && true
                                                                                                            && (true
                                                                                                               ==> true))
                                                                                                        && (x₄₃[N₃₀ - 1 := x[0 := x[1]][1 := x[0]][0]][i₅₀] % 2 != 0
                                                                                                           ==> true
                                                                                                            && 0 <= i₅₀ + 1
                                                                                                            && i₅₀ + 1 <= N₃₀
                                                                                                            && (forall i₂: int ::
                                                                                                                  (  i₂ <= i₂
                                                                                                                    && 0 <= i₂
                                                                                                                    && i₂ < i₅₀ + 1
                                                                                                                     ==> i₂ < N₃₀))
                                                                                                            && true
                                                                                                            && (true
                                                                                                               ==> true)))
                                                                                                    && (!(i₅₀ < N₃₀
                                                                                                    )
                                                                                                       ==> true
                                                                                                        && (true
                                                                                                           ==> (  ret₃₄ != ret₄₀
                                                                                                              || ret₃₄ != ret₄₉
                                                                                                               ==> false
                                                                                                                && (true
                                                                                                                   ==> true))
                                                                                                            && (!(  ret₃₄ != ret₄₀
                                                                                                              || ret₃₄ != ret₄₉
                                                                                                            )
                                                                                                               ==> true))))))))))))))))))))))
              && (!(1 < N₃₀
              )
                 ==> true))));


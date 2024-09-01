data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int ::
      (true
         ==> true
          && 0 <= 0
          && 0 <= N
          && (forall i₄: int ::
                (  i₄ <= i₄
                  && 0 <= i₄
                  && i₄ < 0
                   ==> i₄ < N))
          && (forall i₃₂: int ::
                (  true
                  && 0 <= i₃₂
                  && i₃₂ <= N
                  && (forall i₄: int ::
                        (  i₄ <= i₄
                          && 0 <= i₄
                          && i₄ < i₃₂
                           ==> i₄ < N))
                   ==> (i₃₂ < N
                       ==> true
                        && 0 <= i₃₂ + 1
                        && i₃₂ + 1 <= N
                        && (forall i₄: int ::
                              (  i₄ <= i₄
                                && 0 <= i₄
                                && i₄ < i₃₂ + 1
                                 ==> i₄ < N))
                        && true
                        && (true
                           ==> true))
                    && (!(i₃₂ < N
                    )
                       ==> true
                        && (true
                           ==> true))))));

goal (true
   ==> true
    && (forall N₃₅: int ::
          (true
             ==> (1 < N₃₅
                 ==> (forall x: [int]int ::
                        true
                        && 0 <= 0
                        && 0 <= N₃₅
                        && (forall x₁₅: int ::
                              ((exists i₁₄: int ::
                                      x₁₅ == i₁₄
                                      && 0 <= i₁₄
                                      && i₁₄ < 0)
                                 ==> (exists __VERIFIER_nondet_int₂₁₃: int, i₁₄: int ::
                                        i₁₄ < N₃₅
                                        && x₁₅ == i₁₄
                                        && 0 <= i₁₄
                                        && i₁₄ < 0
                                        && x[x₁₅] == __VERIFIER_nondet_int₂₁₃)))
                        && (forall x₁₅: int ::
                              (!((exists i₁₄: int ::
                                      x₁₅ == i₁₄
                                      && 0 <= i₁₄
                                      && i₁₄ < 0)
                              )
                                 ==> x[x₁₅] == x[x₁₅]))
                        && (forall i₁₄: int ::
                              (  i₁₄ <= i₁₄
                                && 0 <= i₁₄
                                && i₁₄ < 0
                                 ==> i₁₄ < N₃₅))
                        && (forall x₃₆: [int]int, i₃₇: int ::
                              (  true
                                && 0 <= i₃₇
                                && i₃₇ <= N₃₅
                                && (forall x₁₅: int ::
                                      ((exists i₁₄: int ::
                                              x₁₅ == i₁₄
                                              && 0 <= i₁₄
                                              && i₁₄ < i₃₇)
                                         ==> (exists __VERIFIER_nondet_int₂₁₃: int, i₁₄: int ::
                                                i₁₄ < N₃₅
                                                && x₁₅ == i₁₄
                                                && 0 <= i₁₄
                                                && i₁₄ < i₃₇
                                                && x₃₆[x₁₅] == __VERIFIER_nondet_int₂₁₃)))
                                && (forall x₁₅: int ::
                                      (!((exists i₁₄: int ::
                                              x₁₅ == i₁₄
                                              && 0 <= i₁₄
                                              && i₁₄ < i₃₇)
                                      )
                                         ==> x₃₆[x₁₅] == x[x₁₅]))
                                && (forall i₁₄: int ::
                                      (  i₁₄ <= i₁₄
                                        && 0 <= i₁₄
                                        && i₁₄ < i₃₇
                                         ==> i₁₄ < N₃₅))
                                 ==> (i₃₇ < N₃₅
                                     ==> (forall __VERIFIER_nondet_int₂: int ::
                                            true
                                            && 0 <= i₃₇ + 1
                                            && i₃₇ + 1 <= N₃₅
                                            && (forall x₁₅: int ::
                                                  ((exists i₁₄: int ::
                                                          x₁₅ == i₁₄
                                                          && 0 <= i₁₄
                                                          && i₁₄ < i₃₇ + 1)
                                                     ==> (exists __VERIFIER_nondet_int₂₁₃: int, i₁₄: int ::
                                                            i₁₄ < N₃₅
                                                            && x₁₅ == i₁₄
                                                            && 0 <= i₁₄
                                                            && i₁₄ < i₃₇ + 1
                                                            && x₃₆[i₃₇ := __VERIFIER_nondet_int₂][x₁₅] == __VERIFIER_nondet_int₂₁₃)))
                                            && (forall x₁₅: int ::
                                                  (!((exists i₁₄: int ::
                                                          x₁₅ == i₁₄
                                                          && 0 <= i₁₄
                                                          && i₁₄ < i₃₇ + 1)
                                                  )
                                                     ==> x₃₆[i₃₇ := __VERIFIER_nondet_int₂][x₁₅] == x[x₁₅]))
                                            && (forall i₁₄: int ::
                                                  (  i₁₄ <= i₁₄
                                                    && 0 <= i₁₄
                                                    && i₁₄ < i₃₇ + 1
                                                     ==> i₁₄ < N₃₅))
                                            && true
                                            && (true
                                               ==> true)))
                                  && (!(i₃₇ < N₃₅
                                  )
                                     ==> true
                                      && (true
                                         ==> true
                                          && (true
                                             ==> true
                                              && 0 <= 0
                                              && 0 <= N₃₅
                                              && (forall i₄: int ::
                                                    (  i₄ <= i₄
                                                      && 0 <= i₄
                                                      && i₄ < 0
                                                       ==> i₄ < N₃₅))
                                              && (forall ret₄₂: int, i₄₃: int ::
                                                    (  true
                                                      && 0 <= i₄₃
                                                      && i₄₃ <= N₃₅
                                                      && (forall i₄: int ::
                                                            (  i₄ <= i₄
                                                              && 0 <= i₄
                                                              && i₄ < i₄₃
                                                               ==> i₄ < N₃₅))
                                                       ==> (i₄₃ < N₃₅
                                                           ==> true
                                                            && 0 <= i₄₃ + 1
                                                            && i₄₃ + 1 <= N₃₅
                                                            && (forall i₄: int ::
                                                                  (  i₄ <= i₄
                                                                    && 0 <= i₄
                                                                    && i₄ < i₄₃ + 1
                                                                     ==> i₄ < N₃₅))
                                                            && true
                                                            && (true
                                                               ==> true))
                                                        && (!(i₄₃ < N₃₅
                                                        )
                                                           ==> true
                                                            && (true
                                                               ==> true
                                                                && (true
                                                                   ==> true
                                                                    && 0 <= 0
                                                                    && 0 <= N₃₅
                                                                    && (forall i₄: int ::
                                                                          (  i₄ <= i₄
                                                                            && 0 <= i₄
                                                                            && i₄ < 0
                                                                             ==> i₄ < N₃₅))
                                                                    && (forall ret₄₈: int, i₄₉: int ::
                                                                          (  true
                                                                            && 0 <= i₄₉
                                                                            && i₄₉ <= N₃₅
                                                                            && (forall i₄: int ::
                                                                                  (  i₄ <= i₄
                                                                                    && 0 <= i₄
                                                                                    && i₄ < i₄₉
                                                                                     ==> i₄ < N₃₅))
                                                                             ==> (i₄₉ < N₃₅
                                                                                 ==> true
                                                                                  && 0 <= i₄₉ + 1
                                                                                  && i₄₉ + 1 <= N₃₅
                                                                                  && (forall i₄: int ::
                                                                                        (  i₄ <= i₄
                                                                                          && 0 <= i₄
                                                                                          && i₄ < i₄₉ + 1
                                                                                           ==> i₄ < N₃₅))
                                                                                  && true
                                                                                  && (true
                                                                                     ==> true))
                                                                              && (!(i₄₉ < N₃₅
                                                                              )
                                                                                 ==> true
                                                                                  && (true
                                                                                     ==> true
                                                                                      && 0 <= 0
                                                                                      && 0 <= -1 + N₃₅
                                                                                      && (forall x₂₅: int ::
                                                                                            ((exists i₂₄: int ::
                                                                                                    x₂₅ == i₂₄
                                                                                                    && 0 <= i₂₄
                                                                                                    && i₂₄ < 0)
                                                                                               ==> (exists i₂₄: int ::
                                                                                                      i₂₄ < -1 + N₃₅
                                                                                                      && x₂₅ == i₂₄
                                                                                                      && 0 <= i₂₄
                                                                                                      && i₂₄ < 0
                                                                                                      && x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][1 + i₂₄])))
                                                                                      && (forall x₂₅: int ::
                                                                                            (!((exists i₂₄: int ::
                                                                                                    x₂₅ == i₂₄
                                                                                                    && 0 <= i₂₄
                                                                                                    && i₂₄ < 0)
                                                                                            )
                                                                                               ==> x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅]))
                                                                                      && (forall i₂₄: int ::
                                                                                            (  i₂₄ <= i₂₄
                                                                                              && 0 <= i₂₄
                                                                                              && i₂₄ < 0
                                                                                               ==> i₂₄ < -1 + N₃₅))
                                                                                      && (forall x₅₁: [int]int, i₅₂: int ::
                                                                                            (  true
                                                                                              && 0 <= i₅₂
                                                                                              && i₅₂ <= -1 + N₃₅
                                                                                              && (forall x₂₅: int ::
                                                                                                    ((exists i₂₄: int ::
                                                                                                            x₂₅ == i₂₄
                                                                                                            && 0 <= i₂₄
                                                                                                            && i₂₄ < i₅₂)
                                                                                                       ==> (exists i₂₄: int ::
                                                                                                              i₂₄ < -1 + N₃₅
                                                                                                              && x₂₅ == i₂₄
                                                                                                              && 0 <= i₂₄
                                                                                                              && i₂₄ < i₅₂
                                                                                                              && x₅₁[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][1 + i₂₄])))
                                                                                              && (forall x₂₅: int ::
                                                                                                    (!((exists i₂₄: int ::
                                                                                                            x₂₅ == i₂₄
                                                                                                            && 0 <= i₂₄
                                                                                                            && i₂₄ < i₅₂)
                                                                                                    )
                                                                                                       ==> x₅₁[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅]))
                                                                                              && (forall i₂₄: int ::
                                                                                                    (  i₂₄ <= i₂₄
                                                                                                      && 0 <= i₂₄
                                                                                                      && i₂₄ < i₅₂
                                                                                                       ==> i₂₄ < -1 + N₃₅))
                                                                                               ==> (i₅₂ < N₃₅ - 1
                                                                                                   ==> true
                                                                                                    && 0 <= i₅₂ + 1
                                                                                                    && i₅₂ + 1 <= -1 + N₃₅
                                                                                                    && (forall x₂₅: int ::
                                                                                                          ((exists i₂₄: int ::
                                                                                                                  x₂₅ == i₂₄
                                                                                                                  && 0 <= i₂₄
                                                                                                                  && i₂₄ < i₅₂ + 1)
                                                                                                             ==> (exists i₂₄: int ::
                                                                                                                    i₂₄ < -1 + N₃₅
                                                                                                                    && x₂₅ == i₂₄
                                                                                                                    && 0 <= i₂₄
                                                                                                                    && i₂₄ < i₅₂ + 1
                                                                                                                    && x₅₁[i₅₂ := x₅₁[i₅₂ + 1]][x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][1 + i₂₄])))
                                                                                                    && (forall x₂₅: int ::
                                                                                                          (!((exists i₂₄: int ::
                                                                                                                  x₂₅ == i₂₄
                                                                                                                  && 0 <= i₂₄
                                                                                                                  && i₂₄ < i₅₂ + 1)
                                                                                                          )
                                                                                                             ==> x₅₁[i₅₂ := x₅₁[i₅₂ + 1]][x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅]))
                                                                                                    && (forall i₂₄: int ::
                                                                                                          (  i₂₄ <= i₂₄
                                                                                                            && 0 <= i₂₄
                                                                                                            && i₂₄ < i₅₂ + 1
                                                                                                             ==> i₂₄ < -1 + N₃₅))
                                                                                                    && true
                                                                                                    && (true
                                                                                                       ==> true))
                                                                                                && (!(i₅₂ < N₃₅ - 1
                                                                                                )
                                                                                                   ==> true
                                                                                                    && (true
                                                                                                       ==> true
                                                                                                        && (true
                                                                                                           ==> true
                                                                                                            && 0 <= 0
                                                                                                            && 0 <= N₃₅
                                                                                                            && (forall i₄: int ::
                                                                                                                  (  i₄ <= i₄
                                                                                                                    && 0 <= i₄
                                                                                                                    && i₄ < 0
                                                                                                                     ==> i₄ < N₃₅))
                                                                                                            && (forall ret₅₇: int, i₅₈: int ::
                                                                                                                  (  true
                                                                                                                    && 0 <= i₅₈
                                                                                                                    && i₅₈ <= N₃₅
                                                                                                                    && (forall i₄: int ::
                                                                                                                          (  i₄ <= i₄
                                                                                                                            && 0 <= i₄
                                                                                                                            && i₄ < i₅₈
                                                                                                                             ==> i₄ < N₃₅))
                                                                                                                     ==> (i₅₈ < N₃₅
                                                                                                                         ==> true
                                                                                                                          && 0 <= i₅₈ + 1
                                                                                                                          && i₅₈ + 1 <= N₃₅
                                                                                                                          && (forall i₄: int ::
                                                                                                                                (  i₄ <= i₄
                                                                                                                                  && 0 <= i₄
                                                                                                                                  && i₄ < i₅₈ + 1
                                                                                                                                   ==> i₄ < N₃₅))
                                                                                                                          && true
                                                                                                                          && (true
                                                                                                                             ==> true))
                                                                                                                      && (!(i₅₈ < N₃₅
                                                                                                                      )
                                                                                                                         ==> true
                                                                                                                          && (true
                                                                                                                             ==> (  ret₄₂ != ret₄₈
                                                                                                                                || ret₄₂ != ret₅₇
                                                                                                                                 ==> false
                                                                                                                                  && (true
                                                                                                                                     ==> true))
                                                                                                                              && (!(  ret₄₂ != ret₄₈
                                                                                                                                || ret₄₂ != ret₅₇
                                                                                                                              )
                                                                                                                                 ==> true))))))))))))))))))))))))))
              && (!(1 < N₃₅
              )
                 ==> true))));


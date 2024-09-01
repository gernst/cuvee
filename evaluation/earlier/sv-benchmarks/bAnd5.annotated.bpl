data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int ::
      (true
         ==> true
          && 1 <= 1
          && 1 <= N
          && (forall i₄: int ::
                (  i₄ <= i₄
                  && 1 <= i₄
                  && i₄ < 1
                   ==> i₄ < N))
          && (forall i₃₂: int ::
                (  true
                  && 1 <= i₃₂
                  && i₃₂ <= N
                  && (forall i₄: int ::
                        (  i₄ <= i₄
                          && 1 <= i₄
                          && i₄ < i₃₂
                           ==> i₄ < N))
                   ==> (i₃₂ < N
                       ==> true
                        && 1 <= i₃₂ + 1
                        && i₃₂ + 1 <= N
                        && (forall i₄: int ::
                              (  i₄ <= i₄
                                && 1 <= i₄
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
                                              && 1 <= 1
                                              && 1 <= N₃₅
                                              && (forall i₄: int ::
                                                    (  i₄ <= i₄
                                                      && 1 <= i₄
                                                      && i₄ < 1
                                                       ==> i₄ < N₃₅))
                                              && (forall res₄₁: int, i₄₂: int ::
                                                    (  true
                                                      && 1 <= i₄₂
                                                      && i₄₂ <= N₃₅
                                                      && (forall i₄: int ::
                                                            (  i₄ <= i₄
                                                              && 1 <= i₄
                                                              && i₄ < i₄₂
                                                               ==> i₄ < N₃₅))
                                                       ==> (i₄₂ < N₃₅
                                                           ==> true
                                                            && 1 <= i₄₂ + 1
                                                            && i₄₂ + 1 <= N₃₅
                                                            && (forall i₄: int ::
                                                                  (  i₄ <= i₄
                                                                    && 1 <= i₄
                                                                    && i₄ < i₄₂ + 1
                                                                     ==> i₄ < N₃₅))
                                                            && true
                                                            && (true
                                                               ==> true))
                                                        && (!(i₄₂ < N₃₅
                                                        )
                                                           ==> true
                                                            && (true
                                                               ==> true
                                                                && (true
                                                                   ==> true
                                                                    && 1 <= 1
                                                                    && 1 <= N₃₅
                                                                    && (forall i₄: int ::
                                                                          (  i₄ <= i₄
                                                                            && 1 <= i₄
                                                                            && i₄ < 1
                                                                             ==> i₄ < N₃₅))
                                                                    && (forall res₄₇: int, i₄₈: int ::
                                                                          (  true
                                                                            && 1 <= i₄₈
                                                                            && i₄₈ <= N₃₅
                                                                            && (forall i₄: int ::
                                                                                  (  i₄ <= i₄
                                                                                    && 1 <= i₄
                                                                                    && i₄ < i₄₈
                                                                                     ==> i₄ < N₃₅))
                                                                             ==> (i₄₈ < N₃₅
                                                                                 ==> true
                                                                                  && 1 <= i₄₈ + 1
                                                                                  && i₄₈ + 1 <= N₃₅
                                                                                  && (forall i₄: int ::
                                                                                        (  i₄ <= i₄
                                                                                          && 1 <= i₄
                                                                                          && i₄ < i₄₈ + 1
                                                                                           ==> i₄ < N₃₅))
                                                                                  && true
                                                                                  && (true
                                                                                     ==> true))
                                                                              && (!(i₄₈ < N₃₅
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
                                                                                      && (forall x₅₀: [int]int, i₅₁: int ::
                                                                                            (  true
                                                                                              && 0 <= i₅₁
                                                                                              && i₅₁ <= -1 + N₃₅
                                                                                              && (forall x₂₅: int ::
                                                                                                    ((exists i₂₄: int ::
                                                                                                            x₂₅ == i₂₄
                                                                                                            && 0 <= i₂₄
                                                                                                            && i₂₄ < i₅₁)
                                                                                                       ==> (exists i₂₄: int ::
                                                                                                              i₂₄ < -1 + N₃₅
                                                                                                              && x₂₅ == i₂₄
                                                                                                              && 0 <= i₂₄
                                                                                                              && i₂₄ < i₅₁
                                                                                                              && x₅₀[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][1 + i₂₄])))
                                                                                              && (forall x₂₅: int ::
                                                                                                    (!((exists i₂₄: int ::
                                                                                                            x₂₅ == i₂₄
                                                                                                            && 0 <= i₂₄
                                                                                                            && i₂₄ < i₅₁)
                                                                                                    )
                                                                                                       ==> x₅₀[x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅]))
                                                                                              && (forall i₂₄: int ::
                                                                                                    (  i₂₄ <= i₂₄
                                                                                                      && 0 <= i₂₄
                                                                                                      && i₂₄ < i₅₁
                                                                                                       ==> i₂₄ < -1 + N₃₅))
                                                                                               ==> (i₅₁ < N₃₅ - 1
                                                                                                   ==> true
                                                                                                    && 0 <= i₅₁ + 1
                                                                                                    && i₅₁ + 1 <= -1 + N₃₅
                                                                                                    && (forall x₂₅: int ::
                                                                                                          ((exists i₂₄: int ::
                                                                                                                  x₂₅ == i₂₄
                                                                                                                  && 0 <= i₂₄
                                                                                                                  && i₂₄ < i₅₁ + 1)
                                                                                                             ==> (exists i₂₄: int ::
                                                                                                                    i₂₄ < -1 + N₃₅
                                                                                                                    && x₂₅ == i₂₄
                                                                                                                    && 0 <= i₂₄
                                                                                                                    && i₂₄ < i₅₁ + 1
                                                                                                                    && x₅₀[i₅₁ := x₅₀[i₅₁ + 1]][x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][1 + i₂₄])))
                                                                                                    && (forall x₂₅: int ::
                                                                                                          (!((exists i₂₄: int ::
                                                                                                                  x₂₅ == i₂₄
                                                                                                                  && 0 <= i₂₄
                                                                                                                  && i₂₄ < i₅₁ + 1)
                                                                                                          )
                                                                                                             ==> x₅₀[i₅₁ := x₅₀[i₅₁ + 1]][x₂₅] == x₃₆[0 := x₃₆[1]][1 := x₃₆[0]][x₂₅]))
                                                                                                    && (forall i₂₄: int ::
                                                                                                          (  i₂₄ <= i₂₄
                                                                                                            && 0 <= i₂₄
                                                                                                            && i₂₄ < i₅₁ + 1
                                                                                                             ==> i₂₄ < -1 + N₃₅))
                                                                                                    && true
                                                                                                    && (true
                                                                                                       ==> true))
                                                                                                && (!(i₅₁ < N₃₅ - 1
                                                                                                )
                                                                                                   ==> true
                                                                                                    && (true
                                                                                                       ==> true
                                                                                                        && (true
                                                                                                           ==> true
                                                                                                            && 1 <= 1
                                                                                                            && 1 <= N₃₅
                                                                                                            && (forall i₄: int ::
                                                                                                                  (  i₄ <= i₄
                                                                                                                    && 1 <= i₄
                                                                                                                    && i₄ < 1
                                                                                                                     ==> i₄ < N₃₅))
                                                                                                            && (forall res₅₆: int, i₅₇: int ::
                                                                                                                  (  true
                                                                                                                    && 1 <= i₅₇
                                                                                                                    && i₅₇ <= N₃₅
                                                                                                                    && (forall i₄: int ::
                                                                                                                          (  i₄ <= i₄
                                                                                                                            && 1 <= i₄
                                                                                                                            && i₄ < i₅₇
                                                                                                                             ==> i₄ < N₃₅))
                                                                                                                     ==> (i₅₇ < N₃₅
                                                                                                                         ==> true
                                                                                                                          && 1 <= i₅₇ + 1
                                                                                                                          && i₅₇ + 1 <= N₃₅
                                                                                                                          && (forall i₄: int ::
                                                                                                                                (  i₄ <= i₄
                                                                                                                                  && 1 <= i₄
                                                                                                                                  && i₄ < i₅₇ + 1
                                                                                                                                   ==> i₄ < N₃₅))
                                                                                                                          && true
                                                                                                                          && (true
                                                                                                                             ==> true))
                                                                                                                      && (!(i₅₇ < N₃₅
                                                                                                                      )
                                                                                                                         ==> true
                                                                                                                          && (true
                                                                                                                             ==> (  res₄₁ != res₄₇
                                                                                                                                || res₄₁ != res₅₆
                                                                                                                                 ==> false
                                                                                                                                  && (true
                                                                                                                                     ==> true))
                                                                                                                              && (!(  res₄₁ != res₄₇
                                                                                                                                || res₄₁ != res₅₆
                                                                                                                              )
                                                                                                                                 ==> true))))))))))))))))))))))))))
              && (!(1 < N₃₅
              )
                 ==> true))));


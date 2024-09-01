data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int ::
        true
        && 0 <= 0
        && 0 <= 20
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < 0
                 ==> i₂ < 20))
        && (forall i₂₃: int ::
              (  true
                && 0 <= i₂₃
                && i₂₃ <= 20
                && (forall i₂: int ::
                      (  i₂ <= i₂
                        && 0 <= i₂
                        && i₂ < i₂₃
                         ==> i₂ < 20))
                 ==> (i₂₃ < 20
                     ==> (x[i₂₃] % 2 == 0
                         ==> true
                          && 0 <= i₂₃ + 1
                          && i₂₃ + 1 <= 20
                          && (forall i₂: int ::
                                (  i₂ <= i₂
                                  && 0 <= i₂
                                  && i₂ < i₂₃ + 1
                                   ==> i₂ < 20))
                          && true
                          && (true
                             ==> true))
                      && (x[i₂₃] % 2 != 0
                         ==> true
                          && 0 <= i₂₃ + 1
                          && i₂₃ + 1 <= 20
                          && (forall i₂: int ::
                                (  i₂ <= i₂
                                  && 0 <= i₂
                                  && i₂ < i₂₃ + 1
                                   ==> i₂ < 20))
                          && true
                          && (true
                             ==> true)))
                  && (!(i₂₃ < 20
                  )
                     ==> true
                      && (true
                         ==> true)))));

goal (forall x: [int]int ::
        true
        && 0 <= 0
        && 0 <= 20
        && (forall x₁₂: int ::
              ((exists i₁₁: int ::
                      x₁₂ == i₁₁
                      && 0 <= i₁₁
                      && i₁₁ < 0)
                 ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                        i₁₁ < 20
                        && x₁₂ == i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < 0
                        && x[x₁₂] == __VERIFIER_nondet_int₄₁₀)))
        && (forall x₁₂: int ::
              (!((exists i₁₁: int ::
                      x₁₂ == i₁₁
                      && 0 <= i₁₁
                      && i₁₁ < 0)
              )
                 ==> x[x₁₂] == x[x₁₂]))
        && (forall i₁₁: int ::
              (  i₁₁ <= i₁₁
                && 0 <= i₁₁
                && i₁₁ < 0
                 ==> i₁₁ < 20))
        && (forall x₂₈: [int]int, i₂₉: int ::
              (  true
                && 0 <= i₂₉
                && i₂₉ <= 20
                && (forall x₁₂: int ::
                      ((exists i₁₁: int ::
                              x₁₂ == i₁₁
                              && 0 <= i₁₁
                              && i₁₁ < i₂₉)
                         ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                                i₁₁ < 20
                                && x₁₂ == i₁₁
                                && 0 <= i₁₁
                                && i₁₁ < i₂₉
                                && x₂₈[x₁₂] == __VERIFIER_nondet_int₄₁₀)))
                && (forall x₁₂: int ::
                      (!((exists i₁₁: int ::
                              x₁₂ == i₁₁
                              && 0 <= i₁₁
                              && i₁₁ < i₂₉)
                      )
                         ==> x₂₈[x₁₂] == x[x₁₂]))
                && (forall i₁₁: int ::
                      (  i₁₁ <= i₁₁
                        && 0 <= i₁₁
                        && i₁₁ < i₂₉
                         ==> i₁₁ < 20))
                 ==> (i₂₉ < 20
                     ==> (forall __VERIFIER_nondet_int₄: int ::
                            true
                            && 0 <= i₂₉ + 1
                            && i₂₉ + 1 <= 20
                            && (forall x₁₂: int ::
                                  ((exists i₁₁: int ::
                                          x₁₂ == i₁₁
                                          && 0 <= i₁₁
                                          && i₁₁ < i₂₉ + 1)
                                     ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                                            i₁₁ < 20
                                            && x₁₂ == i₁₁
                                            && 0 <= i₁₁
                                            && i₁₁ < i₂₉ + 1
                                            && x₂₈[i₂₉ := __VERIFIER_nondet_int₄][x₁₂] == __VERIFIER_nondet_int₄₁₀)))
                            && (forall x₁₂: int ::
                                  (!((exists i₁₁: int ::
                                          x₁₂ == i₁₁
                                          && 0 <= i₁₁
                                          && i₁₁ < i₂₉ + 1)
                                  )
                                     ==> x₂₈[i₂₉ := __VERIFIER_nondet_int₄][x₁₂] == x[x₁₂]))
                            && (forall i₁₁: int ::
                                  (  i₁₁ <= i₁₁
                                    && 0 <= i₁₁
                                    && i₁₁ < i₂₉ + 1
                                     ==> i₁₁ < 20))
                            && true
                            && (true
                               ==> true)))
                  && (!(i₂₉ < 20
                  )
                     ==> true
                      && (true
                         ==> true
                          && (true
                             ==> true
                              && 0 <= 0
                              && 0 <= 20
                              && (forall i₂: int ::
                                    (  i₂ <= i₂
                                      && 0 <= i₂
                                      && i₂ < 0
                                       ==> i₂ < 20))
                              && (forall ret₃₄: int, i₃₅: int ::
                                    (  true
                                      && 0 <= i₃₅
                                      && i₃₅ <= 20
                                      && (forall i₂: int ::
                                            (  i₂ <= i₂
                                              && 0 <= i₂
                                              && i₂ < i₃₅
                                               ==> i₂ < 20))
                                       ==> (i₃₅ < 20
                                           ==> (x₂₈[i₃₅] % 2 == 0
                                               ==> true
                                                && 0 <= i₃₅ + 1
                                                && i₃₅ + 1 <= 20
                                                && (forall i₂: int ::
                                                      (  i₂ <= i₂
                                                        && 0 <= i₂
                                                        && i₂ < i₃₅ + 1
                                                         ==> i₂ < 20))
                                                && true
                                                && (true
                                                   ==> true))
                                            && (x₂₈[i₃₅] % 2 != 0
                                               ==> true
                                                && 0 <= i₃₅ + 1
                                                && i₃₅ + 1 <= 20
                                                && (forall i₂: int ::
                                                      (  i₂ <= i₂
                                                        && 0 <= i₂
                                                        && i₂ < i₃₅ + 1
                                                         ==> i₂ < 20))
                                                && true
                                                && (true
                                                   ==> true)))
                                        && (!(i₃₅ < 20
                                        )
                                           ==> true
                                            && (true
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 0 <= 0
                                                    && 0 <= 20
                                                    && (forall i₂: int ::
                                                          (  i₂ <= i₂
                                                            && 0 <= i₂
                                                            && i₂ < 0
                                                             ==> i₂ < 20))
                                                    && (forall ret₄₀: int, i₄₁: int ::
                                                          (  true
                                                            && 0 <= i₄₁
                                                            && i₄₁ <= 20
                                                            && (forall i₂: int ::
                                                                  (  i₂ <= i₂
                                                                    && 0 <= i₂
                                                                    && i₂ < i₄₁
                                                                     ==> i₂ < 20))
                                                             ==> (i₄₁ < 20
                                                                 ==> (x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][i₄₁] % 2 == 0
                                                                     ==> true
                                                                      && 0 <= i₄₁ + 1
                                                                      && i₄₁ + 1 <= 20
                                                                      && (forall i₂: int ::
                                                                            (  i₂ <= i₂
                                                                              && 0 <= i₂
                                                                              && i₂ < i₄₁ + 1
                                                                               ==> i₂ < 20))
                                                                      && true
                                                                      && (true
                                                                         ==> true))
                                                                  && (x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][i₄₁] % 2 != 0
                                                                     ==> true
                                                                      && 0 <= i₄₁ + 1
                                                                      && i₄₁ + 1 <= 20
                                                                      && (forall i₂: int ::
                                                                            (  i₂ <= i₂
                                                                              && 0 <= i₂
                                                                              && i₂ < i₄₁ + 1
                                                                               ==> i₂ < 20))
                                                                      && true
                                                                      && (true
                                                                         ==> true)))
                                                              && (!(i₄₁ < 20
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> true
                                                                      && 0 <= 0
                                                                      && 0 <= 19
                                                                      && (forall x₁₈: int ::
                                                                            ((exists i₁₇: int ::
                                                                                    x₁₈ == i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < 0)
                                                                               ==> (exists i₁₇: int ::
                                                                                      i₁₇ < 19
                                                                                      && x₁₈ == i₁₇
                                                                                      && 0 <= i₁₇
                                                                                      && i₁₇ < 0
                                                                                      && x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₁₈] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₇])))
                                                                      && (forall x₁₈: int ::
                                                                            (!((exists i₁₇: int ::
                                                                                    x₁₈ == i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < 0)
                                                                            )
                                                                               ==> x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₁₈] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₁₈]))
                                                                      && (forall i₁₇: int ::
                                                                            (  i₁₇ <= i₁₇
                                                                              && 0 <= i₁₇
                                                                              && i₁₇ < 0
                                                                               ==> i₁₇ < 19))
                                                                      && (forall x₄₃: [int]int, i₄₄: int ::
                                                                            (  true
                                                                              && 0 <= i₄₄
                                                                              && i₄₄ <= 19
                                                                              && (forall x₁₈: int ::
                                                                                    ((exists i₁₇: int ::
                                                                                            x₁₈ == i₁₇
                                                                                            && 0 <= i₁₇
                                                                                            && i₁₇ < i₄₄)
                                                                                       ==> (exists i₁₇: int ::
                                                                                              i₁₇ < 19
                                                                                              && x₁₈ == i₁₇
                                                                                              && 0 <= i₁₇
                                                                                              && i₁₇ < i₄₄
                                                                                              && x₄₃[x₁₈] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₇])))
                                                                              && (forall x₁₈: int ::
                                                                                    (!((exists i₁₇: int ::
                                                                                            x₁₈ == i₁₇
                                                                                            && 0 <= i₁₇
                                                                                            && i₁₇ < i₄₄)
                                                                                    )
                                                                                       ==> x₄₃[x₁₈] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₁₈]))
                                                                              && (forall i₁₇: int ::
                                                                                    (  i₁₇ <= i₁₇
                                                                                      && 0 <= i₁₇
                                                                                      && i₁₇ < i₄₄
                                                                                       ==> i₁₇ < 19))
                                                                               ==> (i₄₄ < 20 - 1
                                                                                   ==> true
                                                                                    && 0 <= i₄₄ + 1
                                                                                    && i₄₄ + 1 <= 19
                                                                                    && (forall x₁₈: int ::
                                                                                          ((exists i₁₇: int ::
                                                                                                  x₁₈ == i₁₇
                                                                                                  && 0 <= i₁₇
                                                                                                  && i₁₇ < i₄₄ + 1)
                                                                                             ==> (exists i₁₇: int ::
                                                                                                    i₁₇ < 19
                                                                                                    && x₁₈ == i₁₇
                                                                                                    && 0 <= i₁₇
                                                                                                    && i₁₇ < i₄₄ + 1
                                                                                                    && x₄₃[i₄₄ := x₄₃[i₄₄ + 1]][x₁₈] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₇])))
                                                                                    && (forall x₁₈: int ::
                                                                                          (!((exists i₁₇: int ::
                                                                                                  x₁₈ == i₁₇
                                                                                                  && 0 <= i₁₇
                                                                                                  && i₁₇ < i₄₄ + 1)
                                                                                          )
                                                                                             ==> x₄₃[i₄₄ := x₄₃[i₄₄ + 1]][x₁₈] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₁₈]))
                                                                                    && (forall i₁₇: int ::
                                                                                          (  i₁₇ <= i₁₇
                                                                                            && 0 <= i₁₇
                                                                                            && i₁₇ < i₄₄ + 1
                                                                                             ==> i₁₇ < 19))
                                                                                    && true
                                                                                    && (true
                                                                                       ==> true))
                                                                                && (!(i₄₄ < 20 - 1
                                                                                )
                                                                                   ==> true
                                                                                    && (true
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 0 <= 0
                                                                                            && 0 <= 20
                                                                                            && (forall i₂: int ::
                                                                                                  (  i₂ <= i₂
                                                                                                    && 0 <= i₂
                                                                                                    && i₂ < 0
                                                                                                     ==> i₂ < 20))
                                                                                            && (forall ret₄₉: int, i₅₀: int ::
                                                                                                  (  true
                                                                                                    && 0 <= i₅₀
                                                                                                    && i₅₀ <= 20
                                                                                                    && (forall i₂: int ::
                                                                                                          (  i₂ <= i₂
                                                                                                            && 0 <= i₂
                                                                                                            && i₂ < i₅₀
                                                                                                             ==> i₂ < 20))
                                                                                                     ==> (i₅₀ < 20
                                                                                                         ==> (x₄₃[20 - 1 := x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][0]][i₅₀] % 2 == 0
                                                                                                             ==> true
                                                                                                              && 0 <= i₅₀ + 1
                                                                                                              && i₅₀ + 1 <= 20
                                                                                                              && (forall i₂: int ::
                                                                                                                    (  i₂ <= i₂
                                                                                                                      && 0 <= i₂
                                                                                                                      && i₂ < i₅₀ + 1
                                                                                                                       ==> i₂ < 20))
                                                                                                              && true
                                                                                                              && (true
                                                                                                                 ==> true))
                                                                                                          && (x₄₃[20 - 1 := x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][0]][i₅₀] % 2 != 0
                                                                                                             ==> true
                                                                                                              && 0 <= i₅₀ + 1
                                                                                                              && i₅₀ + 1 <= 20
                                                                                                              && (forall i₂: int ::
                                                                                                                    (  i₂ <= i₂
                                                                                                                      && 0 <= i₂
                                                                                                                      && i₂ < i₅₀ + 1
                                                                                                                       ==> i₂ < 20))
                                                                                                              && true
                                                                                                              && (true
                                                                                                                 ==> true)))
                                                                                                      && (!(i₅₀ < 20
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
                                                                                                                 ==> true)))))))))))))))))))))))));


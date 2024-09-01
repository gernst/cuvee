data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int ::
        true
        && 0 <= 0
        && 0 <= 60
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < 0
                 ==> i₂ < 60))
        && (forall i₂₃: int ::
              (  true
                && 0 <= i₂₃
                && i₂₃ <= 60
                && (forall i₂: int ::
                      (  i₂ <= i₂
                        && 0 <= i₂
                        && i₂ < i₂₃
                         ==> i₂ < 60))
                 ==> (i₂₃ < 60
                     ==> (x[i₂₃] % 2 == 0
                         ==> true
                          && 0 <= i₂₃ + 1
                          && i₂₃ + 1 <= 60
                          && (forall i₂: int ::
                                (  i₂ <= i₂
                                  && 0 <= i₂
                                  && i₂ < i₂₃ + 1
                                   ==> i₂ < 60))
                          && true
                          && (true
                             ==> true))
                      && (x[i₂₃] % 2 != 0
                         ==> true
                          && 0 <= i₂₃ + 1
                          && i₂₃ + 1 <= 60
                          && (forall i₂: int ::
                                (  i₂ <= i₂
                                  && 0 <= i₂
                                  && i₂ < i₂₃ + 1
                                   ==> i₂ < 60))
                          && true
                          && (true
                             ==> true)))
                  && (!(i₂₃ < 60
                  )
                     ==> true
                      && (true
                         ==> true)))));

goal (forall x: [int]int ::
        true
        && 0 <= 0
        && 0 <= 60
        && (forall x₁₂: int ::
              ((exists i₁₁: int ::
                      x₁₂ == i₁₁
                      && 0 <= i₁₁
                      && i₁₁ < 0)
                 ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                        i₁₁ < 60
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
                 ==> i₁₁ < 60))
        && (forall x₂₈: [int]int, i₂₉: int ::
              (  true
                && 0 <= i₂₉
                && i₂₉ <= 60
                && (forall x₁₂: int ::
                      ((exists i₁₁: int ::
                              x₁₂ == i₁₁
                              && 0 <= i₁₁
                              && i₁₁ < i₂₉)
                         ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                                i₁₁ < 60
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
                         ==> i₁₁ < 60))
                 ==> (i₂₉ < 60
                     ==> (forall __VERIFIER_nondet_int₄: int ::
                            true
                            && 0 <= i₂₉ + 1
                            && i₂₉ + 1 <= 60
                            && (forall x₁₂: int ::
                                  ((exists i₁₁: int ::
                                          x₁₂ == i₁₁
                                          && 0 <= i₁₁
                                          && i₁₁ < i₂₉ + 1)
                                     ==> (exists __VERIFIER_nondet_int₄₁₀: int, i₁₁: int ::
                                            i₁₁ < 60
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
                                     ==> i₁₁ < 60))
                            && true
                            && (true
                               ==> true)))
                  && (!(i₂₉ < 60
                  )
                     ==> true
                      && (true
                         ==> true
                          && (true
                             ==> true
                              && 0 <= 0
                              && 0 <= 60
                              && (forall i₂: int ::
                                    (  i₂ <= i₂
                                      && 0 <= i₂
                                      && i₂ < 0
                                       ==> i₂ < 60))
                              && (forall ret₃₄: int, i₃₅: int ::
                                    (  true
                                      && 0 <= i₃₅
                                      && i₃₅ <= 60
                                      && (forall i₂: int ::
                                            (  i₂ <= i₂
                                              && 0 <= i₂
                                              && i₂ < i₃₅
                                               ==> i₂ < 60))
                                       ==> (i₃₅ < 60
                                           ==> (x₂₈[i₃₅] % 2 == 0
                                               ==> true
                                                && 0 <= i₃₅ + 1
                                                && i₃₅ + 1 <= 60
                                                && (forall i₂: int ::
                                                      (  i₂ <= i₂
                                                        && 0 <= i₂
                                                        && i₂ < i₃₅ + 1
                                                         ==> i₂ < 60))
                                                && true
                                                && (true
                                                   ==> true))
                                            && (x₂₈[i₃₅] % 2 != 0
                                               ==> true
                                                && 0 <= i₃₅ + 1
                                                && i₃₅ + 1 <= 60
                                                && (forall i₂: int ::
                                                      (  i₂ <= i₂
                                                        && 0 <= i₂
                                                        && i₂ < i₃₅ + 1
                                                         ==> i₂ < 60))
                                                && true
                                                && (true
                                                   ==> true)))
                                        && (!(i₃₅ < 60
                                        )
                                           ==> true
                                            && (true
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 0 <= 0
                                                    && 0 <= 60
                                                    && (forall i₂: int ::
                                                          (  i₂ <= i₂
                                                            && 0 <= i₂
                                                            && i₂ < 0
                                                             ==> i₂ < 60))
                                                    && (forall ret₄₀: int, i₄₁: int ::
                                                          (  true
                                                            && 0 <= i₄₁
                                                            && i₄₁ <= 60
                                                            && (forall i₂: int ::
                                                                  (  i₂ <= i₂
                                                                    && 0 <= i₂
                                                                    && i₂ < i₄₁
                                                                     ==> i₂ < 60))
                                                             ==> (i₄₁ < 60
                                                                 ==> (x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][i₄₁] % 2 == 0
                                                                     ==> true
                                                                      && 0 <= i₄₁ + 1
                                                                      && i₄₁ + 1 <= 60
                                                                      && (forall i₂: int ::
                                                                            (  i₂ <= i₂
                                                                              && 0 <= i₂
                                                                              && i₂ < i₄₁ + 1
                                                                               ==> i₂ < 60))
                                                                      && true
                                                                      && (true
                                                                         ==> true))
                                                                  && (x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][i₄₁] % 2 != 0
                                                                     ==> true
                                                                      && 0 <= i₄₁ + 1
                                                                      && i₄₁ + 1 <= 60
                                                                      && (forall i₂: int ::
                                                                            (  i₂ <= i₂
                                                                              && 0 <= i₂
                                                                              && i₂ < i₄₁ + 1
                                                                               ==> i₂ < 60))
                                                                      && true
                                                                      && (true
                                                                         ==> true)))
                                                              && (!(i₄₁ < 60
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> true
                                                                      && 0 <= 0
                                                                      && 0 <= 59
                                                                      && (forall x₁₈: int ::
                                                                            ((exists i₁₇: int ::
                                                                                    x₁₈ == i₁₇
                                                                                    && 0 <= i₁₇
                                                                                    && i₁₇ < 0)
                                                                               ==> (exists i₁₇: int ::
                                                                                      i₁₇ < 59
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
                                                                               ==> i₁₇ < 59))
                                                                      && (forall x₄₃: [int]int, i₄₄: int ::
                                                                            (  true
                                                                              && 0 <= i₄₄
                                                                              && i₄₄ <= 59
                                                                              && (forall x₁₈: int ::
                                                                                    ((exists i₁₇: int ::
                                                                                            x₁₈ == i₁₇
                                                                                            && 0 <= i₁₇
                                                                                            && i₁₇ < i₄₄)
                                                                                       ==> (exists i₁₇: int ::
                                                                                              i₁₇ < 59
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
                                                                                       ==> i₁₇ < 59))
                                                                               ==> (i₄₄ < 60 - 1
                                                                                   ==> true
                                                                                    && 0 <= i₄₄ + 1
                                                                                    && i₄₄ + 1 <= 59
                                                                                    && (forall x₁₈: int ::
                                                                                          ((exists i₁₇: int ::
                                                                                                  x₁₈ == i₁₇
                                                                                                  && 0 <= i₁₇
                                                                                                  && i₁₇ < i₄₄ + 1)
                                                                                             ==> (exists i₁₇: int ::
                                                                                                    i₁₇ < 59
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
                                                                                             ==> i₁₇ < 59))
                                                                                    && true
                                                                                    && (true
                                                                                       ==> true))
                                                                                && (!(i₄₄ < 60 - 1
                                                                                )
                                                                                   ==> true
                                                                                    && (true
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 0 <= 0
                                                                                            && 0 <= 60
                                                                                            && (forall i₂: int ::
                                                                                                  (  i₂ <= i₂
                                                                                                    && 0 <= i₂
                                                                                                    && i₂ < 0
                                                                                                     ==> i₂ < 60))
                                                                                            && (forall ret₄₉: int, i₅₀: int ::
                                                                                                  (  true
                                                                                                    && 0 <= i₅₀
                                                                                                    && i₅₀ <= 60
                                                                                                    && (forall i₂: int ::
                                                                                                          (  i₂ <= i₂
                                                                                                            && 0 <= i₂
                                                                                                            && i₂ < i₅₀
                                                                                                             ==> i₂ < 60))
                                                                                                     ==> (i₅₀ < 60
                                                                                                         ==> (x₄₃[60 - 1 := x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][0]][i₅₀] % 2 == 0
                                                                                                             ==> true
                                                                                                              && 0 <= i₅₀ + 1
                                                                                                              && i₅₀ + 1 <= 60
                                                                                                              && (forall i₂: int ::
                                                                                                                    (  i₂ <= i₂
                                                                                                                      && 0 <= i₂
                                                                                                                      && i₂ < i₅₀ + 1
                                                                                                                       ==> i₂ < 60))
                                                                                                              && true
                                                                                                              && (true
                                                                                                                 ==> true))
                                                                                                          && (x₄₃[60 - 1 := x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][0]][i₅₀] % 2 != 0
                                                                                                             ==> true
                                                                                                              && 0 <= i₅₀ + 1
                                                                                                              && i₅₀ + 1 <= 60
                                                                                                              && (forall i₂: int ::
                                                                                                                    (  i₂ <= i₂
                                                                                                                      && 0 <= i₂
                                                                                                                      && i₂ < i₅₀ + 1
                                                                                                                       ==> i₂ < 60))
                                                                                                              && true
                                                                                                              && (true
                                                                                                                 ==> true)))
                                                                                                      && (!(i₅₀ < 60
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


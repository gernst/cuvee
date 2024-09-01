data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall x: [int]int ::
        true
        && 0 <= 0
        && 0 <= 60
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < 0
                 ==> i₅ < 60))
        && (forall ret₂₅: int, i₂₆: int ::
              (  true
                && 0 <= i₂₆
                && i₂₆ <= 60
                && (forall i₅: int ::
                      (  i₅ <= i₅
                        && 0 <= i₅
                        && i₅ < i₂₆
                         ==> i₅ < 60))
                 ==> (i₂₆ < 60
                     ==> (ret₂₅ < x[i₂₆]
                         ==> true
                          && 0 <= i₂₆ + 1
                          && i₂₆ + 1 <= 60
                          && (forall i₅: int ::
                                (  i₅ <= i₅
                                  && 0 <= i₅
                                  && i₅ < i₂₆ + 1
                                   ==> i₅ < 60))
                          && true
                          && (true
                             ==> true))
                      && (!(ret₂₅ < x[i₂₆]
                      )
                         ==> true
                          && 0 <= i₂₆ + 1
                          && i₂₆ + 1 <= 60
                          && (forall i₅: int ::
                                (  i₅ <= i₅
                                  && 0 <= i₅
                                  && i₅ < i₂₆ + 1
                                   ==> i₅ < 60))
                          && true
                          && (true
                             ==> true)))
                  && (!(i₂₆ < 60
                  )
                     ==> true
                      && (true
                         ==> true)))));

goal (forall x: [int]int ::
        true
        && 0 <= 0
        && 0 <= 60
        && (forall x₁₅: int ::
              ((exists i₁₄: int ::
                      x₁₅ == i₁₄
                      && 0 <= i₁₄
                      && i₁₄ < 0)
                 ==> (exists __VERIFIER_nondet_int₃₁₃: int, i₁₄: int ::
                        i₁₄ < 60
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < 0
                        && x[x₁₅] == __VERIFIER_nondet_int₃₁₃)))
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
                 ==> i₁₄ < 60))
        && (forall x₃₁: [int]int, i₃₂: int ::
              (  true
                && 0 <= i₃₂
                && i₃₂ <= 60
                && (forall x₁₅: int ::
                      ((exists i₁₄: int ::
                              x₁₅ == i₁₄
                              && 0 <= i₁₄
                              && i₁₄ < i₃₂)
                         ==> (exists __VERIFIER_nondet_int₃₁₃: int, i₁₄: int ::
                                i₁₄ < 60
                                && x₁₅ == i₁₄
                                && 0 <= i₁₄
                                && i₁₄ < i₃₂
                                && x₃₁[x₁₅] == __VERIFIER_nondet_int₃₁₃)))
                && (forall x₁₅: int ::
                      (!((exists i₁₄: int ::
                              x₁₅ == i₁₄
                              && 0 <= i₁₄
                              && i₁₄ < i₃₂)
                      )
                         ==> x₃₁[x₁₅] == x[x₁₅]))
                && (forall i₁₄: int ::
                      (  i₁₄ <= i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₂
                         ==> i₁₄ < 60))
                 ==> (i₃₂ < 60
                     ==> (forall __VERIFIER_nondet_int₃: int ::
                            true
                            && 0 <= i₃₂ + 1
                            && i₃₂ + 1 <= 60
                            && (forall x₁₅: int ::
                                  ((exists i₁₄: int ::
                                          x₁₅ == i₁₄
                                          && 0 <= i₁₄
                                          && i₁₄ < i₃₂ + 1)
                                     ==> (exists __VERIFIER_nondet_int₃₁₃: int, i₁₄: int ::
                                            i₁₄ < 60
                                            && x₁₅ == i₁₄
                                            && 0 <= i₁₄
                                            && i₁₄ < i₃₂ + 1
                                            && x₃₁[i₃₂ := __VERIFIER_nondet_int₃][x₁₅] == __VERIFIER_nondet_int₃₁₃)))
                            && (forall x₁₅: int ::
                                  (!((exists i₁₄: int ::
                                          x₁₅ == i₁₄
                                          && 0 <= i₁₄
                                          && i₁₄ < i₃₂ + 1)
                                  )
                                     ==> x₃₁[i₃₂ := __VERIFIER_nondet_int₃][x₁₅] == x[x₁₅]))
                            && (forall i₁₄: int ::
                                  (  i₁₄ <= i₁₄
                                    && 0 <= i₁₄
                                    && i₁₄ < i₃₂ + 1
                                     ==> i₁₄ < 60))
                            && true
                            && (true
                               ==> true)))
                  && (!(i₃₂ < 60
                  )
                     ==> true
                      && (true
                         ==> true
                          && (true
                             ==> true
                              && 0 <= 0
                              && 0 <= 60
                              && (forall i₅: int ::
                                    (  i₅ <= i₅
                                      && 0 <= i₅
                                      && i₅ < 0
                                       ==> i₅ < 60))
                              && (forall ret₃₇: int, i₃₈: int ::
                                    (  true
                                      && 0 <= i₃₈
                                      && i₃₈ <= 60
                                      && (forall i₅: int ::
                                            (  i₅ <= i₅
                                              && 0 <= i₅
                                              && i₅ < i₃₈
                                               ==> i₅ < 60))
                                       ==> (i₃₈ < 60
                                           ==> (ret₃₇ < x₃₁[i₃₈]
                                               ==> true
                                                && 0 <= i₃₈ + 1
                                                && i₃₈ + 1 <= 60
                                                && (forall i₅: int ::
                                                      (  i₅ <= i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₃₈ + 1
                                                         ==> i₅ < 60))
                                                && true
                                                && (true
                                                   ==> true))
                                            && (!(ret₃₇ < x₃₁[i₃₈]
                                            )
                                               ==> true
                                                && 0 <= i₃₈ + 1
                                                && i₃₈ + 1 <= 60
                                                && (forall i₅: int ::
                                                      (  i₅ <= i₅
                                                        && 0 <= i₅
                                                        && i₅ < i₃₈ + 1
                                                         ==> i₅ < 60))
                                                && true
                                                && (true
                                                   ==> true)))
                                        && (!(i₃₈ < 60
                                        )
                                           ==> true
                                            && (true
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 0 <= 0
                                                    && 0 <= 60
                                                    && (forall i₅: int ::
                                                          (  i₅ <= i₅
                                                            && 0 <= i₅
                                                            && i₅ < 0
                                                             ==> i₅ < 60))
                                                    && (forall ret₄₃: int, i₄₄: int ::
                                                          (  true
                                                            && 0 <= i₄₄
                                                            && i₄₄ <= 60
                                                            && (forall i₅: int ::
                                                                  (  i₅ <= i₅
                                                                    && 0 <= i₅
                                                                    && i₅ < i₄₄
                                                                     ==> i₅ < 60))
                                                             ==> (i₄₄ < 60
                                                                 ==> (ret₄₃ < x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][i₄₄]
                                                                     ==> true
                                                                      && 0 <= i₄₄ + 1
                                                                      && i₄₄ + 1 <= 60
                                                                      && (forall i₅: int ::
                                                                            (  i₅ <= i₅
                                                                              && 0 <= i₅
                                                                              && i₅ < i₄₄ + 1
                                                                               ==> i₅ < 60))
                                                                      && true
                                                                      && (true
                                                                         ==> true))
                                                                  && (!(ret₄₃ < x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][i₄₄]
                                                                  )
                                                                     ==> true
                                                                      && 0 <= i₄₄ + 1
                                                                      && i₄₄ + 1 <= 60
                                                                      && (forall i₅: int ::
                                                                            (  i₅ <= i₅
                                                                              && 0 <= i₅
                                                                              && i₅ < i₄₄ + 1
                                                                               ==> i₅ < 60))
                                                                      && true
                                                                      && (true
                                                                         ==> true)))
                                                              && (!(i₄₄ < 60
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> true
                                                                      && 0 <= 0
                                                                      && 0 <= 59
                                                                      && (forall x₂₁: int ::
                                                                            ((exists i₂₀: int ::
                                                                                    x₂₁ == i₂₀
                                                                                    && 0 <= i₂₀
                                                                                    && i₂₀ < 0)
                                                                               ==> (exists i₂₀: int ::
                                                                                      i₂₀ < 59
                                                                                      && x₂₁ == i₂₀
                                                                                      && 0 <= i₂₀
                                                                                      && i₂₀ < 0
                                                                                      && x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][x₂₁] == x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][1 + i₂₀])))
                                                                      && (forall x₂₁: int ::
                                                                            (!((exists i₂₀: int ::
                                                                                    x₂₁ == i₂₀
                                                                                    && 0 <= i₂₀
                                                                                    && i₂₀ < 0)
                                                                            )
                                                                               ==> x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][x₂₁] == x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][x₂₁]))
                                                                      && (forall i₂₀: int ::
                                                                            (  i₂₀ <= i₂₀
                                                                              && 0 <= i₂₀
                                                                              && i₂₀ < 0
                                                                               ==> i₂₀ < 59))
                                                                      && (forall x₄₆: [int]int, i₄₇: int ::
                                                                            (  true
                                                                              && 0 <= i₄₇
                                                                              && i₄₇ <= 59
                                                                              && (forall x₂₁: int ::
                                                                                    ((exists i₂₀: int ::
                                                                                            x₂₁ == i₂₀
                                                                                            && 0 <= i₂₀
                                                                                            && i₂₀ < i₄₇)
                                                                                       ==> (exists i₂₀: int ::
                                                                                              i₂₀ < 59
                                                                                              && x₂₁ == i₂₀
                                                                                              && 0 <= i₂₀
                                                                                              && i₂₀ < i₄₇
                                                                                              && x₄₆[x₂₁] == x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][1 + i₂₀])))
                                                                              && (forall x₂₁: int ::
                                                                                    (!((exists i₂₀: int ::
                                                                                            x₂₁ == i₂₀
                                                                                            && 0 <= i₂₀
                                                                                            && i₂₀ < i₄₇)
                                                                                    )
                                                                                       ==> x₄₆[x₂₁] == x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][x₂₁]))
                                                                              && (forall i₂₀: int ::
                                                                                    (  i₂₀ <= i₂₀
                                                                                      && 0 <= i₂₀
                                                                                      && i₂₀ < i₄₇
                                                                                       ==> i₂₀ < 59))
                                                                               ==> (i₄₇ < 60 - 1
                                                                                   ==> true
                                                                                    && 0 <= i₄₇ + 1
                                                                                    && i₄₇ + 1 <= 59
                                                                                    && (forall x₂₁: int ::
                                                                                          ((exists i₂₀: int ::
                                                                                                  x₂₁ == i₂₀
                                                                                                  && 0 <= i₂₀
                                                                                                  && i₂₀ < i₄₇ + 1)
                                                                                             ==> (exists i₂₀: int ::
                                                                                                    i₂₀ < 59
                                                                                                    && x₂₁ == i₂₀
                                                                                                    && 0 <= i₂₀
                                                                                                    && i₂₀ < i₄₇ + 1
                                                                                                    && x₄₆[i₄₇ := x₄₆[i₄₇ + 1]][x₂₁] == x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][1 + i₂₀])))
                                                                                    && (forall x₂₁: int ::
                                                                                          (!((exists i₂₀: int ::
                                                                                                  x₂₁ == i₂₀
                                                                                                  && 0 <= i₂₀
                                                                                                  && i₂₀ < i₄₇ + 1)
                                                                                          )
                                                                                             ==> x₄₆[i₄₇ := x₄₆[i₄₇ + 1]][x₂₁] == x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][x₂₁]))
                                                                                    && (forall i₂₀: int ::
                                                                                          (  i₂₀ <= i₂₀
                                                                                            && 0 <= i₂₀
                                                                                            && i₂₀ < i₄₇ + 1
                                                                                             ==> i₂₀ < 59))
                                                                                    && true
                                                                                    && (true
                                                                                       ==> true))
                                                                                && (!(i₄₇ < 60 - 1
                                                                                )
                                                                                   ==> true
                                                                                    && (true
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 0 <= 0
                                                                                            && 0 <= 60
                                                                                            && (forall i₅: int ::
                                                                                                  (  i₅ <= i₅
                                                                                                    && 0 <= i₅
                                                                                                    && i₅ < 0
                                                                                                     ==> i₅ < 60))
                                                                                            && (forall ret₅₂: int, i₅₃: int ::
                                                                                                  (  true
                                                                                                    && 0 <= i₅₃
                                                                                                    && i₅₃ <= 60
                                                                                                    && (forall i₅: int ::
                                                                                                          (  i₅ <= i₅
                                                                                                            && 0 <= i₅
                                                                                                            && i₅ < i₅₃
                                                                                                             ==> i₅ < 60))
                                                                                                     ==> (i₅₃ < 60
                                                                                                         ==> (ret₅₂ < x₄₆[60 - 1 := x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][0]][i₅₃]
                                                                                                             ==> true
                                                                                                              && 0 <= i₅₃ + 1
                                                                                                              && i₅₃ + 1 <= 60
                                                                                                              && (forall i₅: int ::
                                                                                                                    (  i₅ <= i₅
                                                                                                                      && 0 <= i₅
                                                                                                                      && i₅ < i₅₃ + 1
                                                                                                                       ==> i₅ < 60))
                                                                                                              && true
                                                                                                              && (true
                                                                                                                 ==> true))
                                                                                                          && (!(ret₅₂ < x₄₆[60 - 1 := x₃₁[0 := x₃₁[1]][1 := x₃₁[0]][0]][i₅₃]
                                                                                                          )
                                                                                                             ==> true
                                                                                                              && 0 <= i₅₃ + 1
                                                                                                              && i₅₃ + 1 <= 60
                                                                                                              && (forall i₅: int ::
                                                                                                                    (  i₅ <= i₅
                                                                                                                      && 0 <= i₅
                                                                                                                      && i₅ < i₅₃ + 1
                                                                                                                       ==> i₅ < 60))
                                                                                                              && true
                                                                                                              && (true
                                                                                                                 ==> true)))
                                                                                                      && (!(i₅₃ < 60
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
                                                                                                                 ==> true)))))))))))))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal true
  && 0 <= 0
  && 0 <= 5
  && (forall i₄: int ::
        (  i₄ <= i₄
          && 0 <= i₄
          && i₄ < 0
           ==> i₄ < 5))
  && (forall i₂₅: int ::
        (  true
          && 0 <= i₂₅
          && i₂₅ <= 5
          && (forall i₄: int ::
                (  i₄ <= i₄
                  && 0 <= i₄
                  && i₄ < i₂₅
                   ==> i₄ < 5))
           ==> (i₂₅ < 5
               ==> true
                && 0 <= i₂₅ + 1
                && i₂₅ + 1 <= 5
                && (forall i₄: int ::
                      (  i₄ <= i₄
                        && 0 <= i₄
                        && i₄ < i₂₅ + 1
                         ==> i₄ < 5))
                && true
                && (true
                   ==> true))
            && (!(i₂₅ < 5
            )
               ==> true
                && (true
                   ==> true))));

goal (forall x: [int]int ::
        true
        && 0 <= 0
        && 0 <= 5
        && (forall x₁₄: int ::
              ((exists i₁₃: int ::
                      x₁₄ == i₁₃
                      && 0 <= i₁₃
                      && i₁₃ < 0)
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                        i₁₃ < 5
                        && x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < 0
                        && x[x₁₄] == __VERIFIER_nondet_int₂₁₂)))
        && (forall x₁₄: int ::
              (!((exists i₁₃: int ::
                      x₁₄ == i₁₃
                      && 0 <= i₁₃
                      && i₁₃ < 0)
              )
                 ==> x[x₁₄] == x[x₁₄]))
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < 0
                 ==> i₁₃ < 5))
        && (forall x₂₈: [int]int, i₂₉: int ::
              (  true
                && 0 <= i₂₉
                && i₂₉ <= 5
                && (forall x₁₄: int ::
                      ((exists i₁₃: int ::
                              x₁₄ == i₁₃
                              && 0 <= i₁₃
                              && i₁₃ < i₂₉)
                         ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                                i₁₃ < 5
                                && x₁₄ == i₁₃
                                && 0 <= i₁₃
                                && i₁₃ < i₂₉
                                && x₂₈[x₁₄] == __VERIFIER_nondet_int₂₁₂)))
                && (forall x₁₄: int ::
                      (!((exists i₁₃: int ::
                              x₁₄ == i₁₃
                              && 0 <= i₁₃
                              && i₁₃ < i₂₉)
                      )
                         ==> x₂₈[x₁₄] == x[x₁₄]))
                && (forall i₁₃: int ::
                      (  i₁₃ <= i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₂₉
                         ==> i₁₃ < 5))
                 ==> (i₂₉ < 5
                     ==> (forall __VERIFIER_nondet_int₂: int ::
                            true
                            && 0 <= i₂₉ + 1
                            && i₂₉ + 1 <= 5
                            && (forall x₁₄: int ::
                                  ((exists i₁₃: int ::
                                          x₁₄ == i₁₃
                                          && 0 <= i₁₃
                                          && i₁₃ < i₂₉ + 1)
                                     ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                                            i₁₃ < 5
                                            && x₁₄ == i₁₃
                                            && 0 <= i₁₃
                                            && i₁₃ < i₂₉ + 1
                                            && x₂₈[i₂₉ := __VERIFIER_nondet_int₂][x₁₄] == __VERIFIER_nondet_int₂₁₂)))
                            && (forall x₁₄: int ::
                                  (!((exists i₁₃: int ::
                                          x₁₄ == i₁₃
                                          && 0 <= i₁₃
                                          && i₁₃ < i₂₉ + 1)
                                  )
                                     ==> x₂₈[i₂₉ := __VERIFIER_nondet_int₂][x₁₄] == x[x₁₄]))
                            && (forall i₁₃: int ::
                                  (  i₁₃ <= i₁₃
                                    && 0 <= i₁₃
                                    && i₁₃ < i₂₉ + 1
                                     ==> i₁₃ < 5))
                            && true
                            && (true
                               ==> true)))
                  && (!(i₂₉ < 5
                  )
                     ==> true
                      && (true
                         ==> true
                          && (true
                             ==> true
                              && 0 <= 0
                              && 0 <= 5
                              && (forall i₄: int ::
                                    (  i₄ <= i₄
                                      && 0 <= i₄
                                      && i₄ < 0
                                       ==> i₄ < 5))
                              && (forall ret₃₄: int, i₃₅: int ::
                                    (  true
                                      && 0 <= i₃₅
                                      && i₃₅ <= 5
                                      && (forall i₄: int ::
                                            (  i₄ <= i₄
                                              && 0 <= i₄
                                              && i₄ < i₃₅
                                               ==> i₄ < 5))
                                       ==> (i₃₅ < 5
                                           ==> true
                                            && 0 <= i₃₅ + 1
                                            && i₃₅ + 1 <= 5
                                            && (forall i₄: int ::
                                                  (  i₄ <= i₄
                                                    && 0 <= i₄
                                                    && i₄ < i₃₅ + 1
                                                     ==> i₄ < 5))
                                            && true
                                            && (true
                                               ==> true))
                                        && (!(i₃₅ < 5
                                        )
                                           ==> true
                                            && (true
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 0 <= 0
                                                    && 0 <= 5
                                                    && (forall i₄: int ::
                                                          (  i₄ <= i₄
                                                            && 0 <= i₄
                                                            && i₄ < 0
                                                             ==> i₄ < 5))
                                                    && (forall ret₄₀: int, i₄₁: int ::
                                                          (  true
                                                            && 0 <= i₄₁
                                                            && i₄₁ <= 5
                                                            && (forall i₄: int ::
                                                                  (  i₄ <= i₄
                                                                    && 0 <= i₄
                                                                    && i₄ < i₄₁
                                                                     ==> i₄ < 5))
                                                             ==> (i₄₁ < 5
                                                                 ==> true
                                                                  && 0 <= i₄₁ + 1
                                                                  && i₄₁ + 1 <= 5
                                                                  && (forall i₄: int ::
                                                                        (  i₄ <= i₄
                                                                          && 0 <= i₄
                                                                          && i₄ < i₄₁ + 1
                                                                           ==> i₄ < 5))
                                                                  && true
                                                                  && (true
                                                                     ==> true))
                                                              && (!(i₄₁ < 5
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> true
                                                                      && 0 <= 0
                                                                      && 0 <= 4
                                                                      && (forall x₂₀: int ::
                                                                            ((exists i₁₉: int ::
                                                                                    x₂₀ == i₁₉
                                                                                    && 0 <= i₁₉
                                                                                    && i₁₉ < 0)
                                                                               ==> (exists i₁₉: int ::
                                                                                      i₁₉ < 4
                                                                                      && x₂₀ == i₁₉
                                                                                      && 0 <= i₁₉
                                                                                      && i₁₉ < 0
                                                                                      && x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₉])))
                                                                      && (forall x₂₀: int ::
                                                                            (!((exists i₁₉: int ::
                                                                                    x₂₀ == i₁₉
                                                                                    && 0 <= i₁₉
                                                                                    && i₁₉ < 0)
                                                                            )
                                                                               ==> x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀]))
                                                                      && (forall i₁₉: int ::
                                                                            (  i₁₉ <= i₁₉
                                                                              && 0 <= i₁₉
                                                                              && i₁₉ < 0
                                                                               ==> i₁₉ < 4))
                                                                      && (forall x₄₃: [int]int, i₄₄: int ::
                                                                            (  true
                                                                              && 0 <= i₄₄
                                                                              && i₄₄ <= 4
                                                                              && (forall x₂₀: int ::
                                                                                    ((exists i₁₉: int ::
                                                                                            x₂₀ == i₁₉
                                                                                            && 0 <= i₁₉
                                                                                            && i₁₉ < i₄₄)
                                                                                       ==> (exists i₁₉: int ::
                                                                                              i₁₉ < 4
                                                                                              && x₂₀ == i₁₉
                                                                                              && 0 <= i₁₉
                                                                                              && i₁₉ < i₄₄
                                                                                              && x₄₃[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₉])))
                                                                              && (forall x₂₀: int ::
                                                                                    (!((exists i₁₉: int ::
                                                                                            x₂₀ == i₁₉
                                                                                            && 0 <= i₁₉
                                                                                            && i₁₉ < i₄₄)
                                                                                    )
                                                                                       ==> x₄₃[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀]))
                                                                              && (forall i₁₉: int ::
                                                                                    (  i₁₉ <= i₁₉
                                                                                      && 0 <= i₁₉
                                                                                      && i₁₉ < i₄₄
                                                                                       ==> i₁₉ < 4))
                                                                               ==> (i₄₄ < 5 - 1
                                                                                   ==> true
                                                                                    && 0 <= i₄₄ + 1
                                                                                    && i₄₄ + 1 <= 4
                                                                                    && (forall x₂₀: int ::
                                                                                          ((exists i₁₉: int ::
                                                                                                  x₂₀ == i₁₉
                                                                                                  && 0 <= i₁₉
                                                                                                  && i₁₉ < i₄₄ + 1)
                                                                                             ==> (exists i₁₉: int ::
                                                                                                    i₁₉ < 4
                                                                                                    && x₂₀ == i₁₉
                                                                                                    && 0 <= i₁₉
                                                                                                    && i₁₉ < i₄₄ + 1
                                                                                                    && x₄₃[i₄₄ := x₄₃[i₄₄ + 1]][x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₉])))
                                                                                    && (forall x₂₀: int ::
                                                                                          (!((exists i₁₉: int ::
                                                                                                  x₂₀ == i₁₉
                                                                                                  && 0 <= i₁₉
                                                                                                  && i₁₉ < i₄₄ + 1)
                                                                                          )
                                                                                             ==> x₄₃[i₄₄ := x₄₃[i₄₄ + 1]][x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀]))
                                                                                    && (forall i₁₉: int ::
                                                                                          (  i₁₉ <= i₁₉
                                                                                            && 0 <= i₁₉
                                                                                            && i₁₉ < i₄₄ + 1
                                                                                             ==> i₁₉ < 4))
                                                                                    && true
                                                                                    && (true
                                                                                       ==> true))
                                                                                && (!(i₄₄ < 5 - 1
                                                                                )
                                                                                   ==> true
                                                                                    && (true
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 0 <= 0
                                                                                            && 0 <= 5
                                                                                            && (forall i₄: int ::
                                                                                                  (  i₄ <= i₄
                                                                                                    && 0 <= i₄
                                                                                                    && i₄ < 0
                                                                                                     ==> i₄ < 5))
                                                                                            && (forall ret₄₉: int, i₅₀: int ::
                                                                                                  (  true
                                                                                                    && 0 <= i₅₀
                                                                                                    && i₅₀ <= 5
                                                                                                    && (forall i₄: int ::
                                                                                                          (  i₄ <= i₄
                                                                                                            && 0 <= i₄
                                                                                                            && i₄ < i₅₀
                                                                                                             ==> i₄ < 5))
                                                                                                     ==> (i₅₀ < 5
                                                                                                         ==> true
                                                                                                          && 0 <= i₅₀ + 1
                                                                                                          && i₅₀ + 1 <= 5
                                                                                                          && (forall i₄: int ::
                                                                                                                (  i₄ <= i₄
                                                                                                                  && 0 <= i₄
                                                                                                                  && i₄ < i₅₀ + 1
                                                                                                                   ==> i₄ < 5))
                                                                                                          && true
                                                                                                          && (true
                                                                                                             ==> true))
                                                                                                      && (!(i₅₀ < 5
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


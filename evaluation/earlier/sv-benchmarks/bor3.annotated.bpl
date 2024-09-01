data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal true
  && 1 <= 1
  && 1 <= 10000
  && (forall i₄: int ::
        (  i₄ <= i₄
          && 1 <= i₄
          && i₄ < 1
           ==> i₄ < 10000))
  && (forall i₂₅: int ::
        (  true
          && 1 <= i₂₅
          && i₂₅ <= 10000
          && (forall i₄: int ::
                (  i₄ <= i₄
                  && 1 <= i₄
                  && i₄ < i₂₅
                   ==> i₄ < 10000))
           ==> (i₂₅ < 10000
               ==> true
                && 1 <= i₂₅ + 1
                && i₂₅ + 1 <= 10000
                && (forall i₄: int ::
                      (  i₄ <= i₄
                        && 1 <= i₄
                        && i₄ < i₂₅ + 1
                         ==> i₄ < 10000))
                && true
                && (true
                   ==> true))
            && (!(i₂₅ < 10000
            )
               ==> true
                && (true
                   ==> true))));

goal (forall x: [int]int ::
        true
        && 0 <= 0
        && 0 <= 10000
        && (forall x₁₄: int ::
              ((exists i₁₃: int ::
                      x₁₄ == i₁₃
                      && 0 <= i₁₃
                      && i₁₃ < 0)
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                        i₁₃ < 10000
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
                 ==> i₁₃ < 10000))
        && (forall x₂₈: [int]int, i₂₉: int ::
              (  true
                && 0 <= i₂₉
                && i₂₉ <= 10000
                && (forall x₁₄: int ::
                      ((exists i₁₃: int ::
                              x₁₄ == i₁₃
                              && 0 <= i₁₃
                              && i₁₃ < i₂₉)
                         ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                                i₁₃ < 10000
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
                         ==> i₁₃ < 10000))
                 ==> (i₂₉ < 10000
                     ==> (forall __VERIFIER_nondet_int₂: int ::
                            true
                            && 0 <= i₂₉ + 1
                            && i₂₉ + 1 <= 10000
                            && (forall x₁₄: int ::
                                  ((exists i₁₃: int ::
                                          x₁₄ == i₁₃
                                          && 0 <= i₁₃
                                          && i₁₃ < i₂₉ + 1)
                                     ==> (exists __VERIFIER_nondet_int₂₁₂: int, i₁₃: int ::
                                            i₁₃ < 10000
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
                                     ==> i₁₃ < 10000))
                            && true
                            && (true
                               ==> true)))
                  && (!(i₂₉ < 10000
                  )
                     ==> true
                      && (true
                         ==> true
                          && (true
                             ==> true
                              && 1 <= 1
                              && 1 <= 10000
                              && (forall i₄: int ::
                                    (  i₄ <= i₄
                                      && 1 <= i₄
                                      && i₄ < 1
                                       ==> i₄ < 10000))
                              && (forall res₃₃: int, i₃₄: int ::
                                    (  true
                                      && 1 <= i₃₄
                                      && i₃₄ <= 10000
                                      && (forall i₄: int ::
                                            (  i₄ <= i₄
                                              && 1 <= i₄
                                              && i₄ < i₃₄
                                               ==> i₄ < 10000))
                                       ==> (i₃₄ < 10000
                                           ==> true
                                            && 1 <= i₃₄ + 1
                                            && i₃₄ + 1 <= 10000
                                            && (forall i₄: int ::
                                                  (  i₄ <= i₄
                                                    && 1 <= i₄
                                                    && i₄ < i₃₄ + 1
                                                     ==> i₄ < 10000))
                                            && true
                                            && (true
                                               ==> true))
                                        && (!(i₃₄ < 10000
                                        )
                                           ==> true
                                            && (true
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 1 <= 1
                                                    && 1 <= 10000
                                                    && (forall i₄: int ::
                                                          (  i₄ <= i₄
                                                            && 1 <= i₄
                                                            && i₄ < 1
                                                             ==> i₄ < 10000))
                                                    && (forall res₃₉: int, i₄₀: int ::
                                                          (  true
                                                            && 1 <= i₄₀
                                                            && i₄₀ <= 10000
                                                            && (forall i₄: int ::
                                                                  (  i₄ <= i₄
                                                                    && 1 <= i₄
                                                                    && i₄ < i₄₀
                                                                     ==> i₄ < 10000))
                                                             ==> (i₄₀ < 10000
                                                                 ==> true
                                                                  && 1 <= i₄₀ + 1
                                                                  && i₄₀ + 1 <= 10000
                                                                  && (forall i₄: int ::
                                                                        (  i₄ <= i₄
                                                                          && 1 <= i₄
                                                                          && i₄ < i₄₀ + 1
                                                                           ==> i₄ < 10000))
                                                                  && true
                                                                  && (true
                                                                     ==> true))
                                                              && (!(i₄₀ < 10000
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> true
                                                                      && 0 <= 0
                                                                      && 0 <= 9999
                                                                      && (forall x₂₀: int ::
                                                                            ((exists i₁₉: int ::
                                                                                    x₂₀ == i₁₉
                                                                                    && 0 <= i₁₉
                                                                                    && i₁₉ < 0)
                                                                               ==> (exists i₁₉: int ::
                                                                                      i₁₉ < 9999
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
                                                                               ==> i₁₉ < 9999))
                                                                      && (forall x₄₂: [int]int, i₄₃: int ::
                                                                            (  true
                                                                              && 0 <= i₄₃
                                                                              && i₄₃ <= 9999
                                                                              && (forall x₂₀: int ::
                                                                                    ((exists i₁₉: int ::
                                                                                            x₂₀ == i₁₉
                                                                                            && 0 <= i₁₉
                                                                                            && i₁₉ < i₄₃)
                                                                                       ==> (exists i₁₉: int ::
                                                                                              i₁₉ < 9999
                                                                                              && x₂₀ == i₁₉
                                                                                              && 0 <= i₁₉
                                                                                              && i₁₉ < i₄₃
                                                                                              && x₄₂[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₉])))
                                                                              && (forall x₂₀: int ::
                                                                                    (!((exists i₁₉: int ::
                                                                                            x₂₀ == i₁₉
                                                                                            && 0 <= i₁₉
                                                                                            && i₁₉ < i₄₃)
                                                                                    )
                                                                                       ==> x₄₂[x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀]))
                                                                              && (forall i₁₉: int ::
                                                                                    (  i₁₉ <= i₁₉
                                                                                      && 0 <= i₁₉
                                                                                      && i₁₉ < i₄₃
                                                                                       ==> i₁₉ < 9999))
                                                                               ==> (i₄₃ < 10000 - 1
                                                                                   ==> true
                                                                                    && 0 <= i₄₃ + 1
                                                                                    && i₄₃ + 1 <= 9999
                                                                                    && (forall x₂₀: int ::
                                                                                          ((exists i₁₉: int ::
                                                                                                  x₂₀ == i₁₉
                                                                                                  && 0 <= i₁₉
                                                                                                  && i₁₉ < i₄₃ + 1)
                                                                                             ==> (exists i₁₉: int ::
                                                                                                    i₁₉ < 9999
                                                                                                    && x₂₀ == i₁₉
                                                                                                    && 0 <= i₁₉
                                                                                                    && i₁₉ < i₄₃ + 1
                                                                                                    && x₄₂[i₄₃ := x₄₂[i₄₃ + 1]][x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][1 + i₁₉])))
                                                                                    && (forall x₂₀: int ::
                                                                                          (!((exists i₁₉: int ::
                                                                                                  x₂₀ == i₁₉
                                                                                                  && 0 <= i₁₉
                                                                                                  && i₁₉ < i₄₃ + 1)
                                                                                          )
                                                                                             ==> x₄₂[i₄₃ := x₄₂[i₄₃ + 1]][x₂₀] == x₂₈[0 := x₂₈[1]][1 := x₂₈[0]][x₂₀]))
                                                                                    && (forall i₁₉: int ::
                                                                                          (  i₁₉ <= i₁₉
                                                                                            && 0 <= i₁₉
                                                                                            && i₁₉ < i₄₃ + 1
                                                                                             ==> i₁₉ < 9999))
                                                                                    && true
                                                                                    && (true
                                                                                       ==> true))
                                                                                && (!(i₄₃ < 10000 - 1
                                                                                )
                                                                                   ==> true
                                                                                    && (true
                                                                                       ==> true
                                                                                        && (true
                                                                                           ==> true
                                                                                            && 1 <= 1
                                                                                            && 1 <= 10000
                                                                                            && (forall i₄: int ::
                                                                                                  (  i₄ <= i₄
                                                                                                    && 1 <= i₄
                                                                                                    && i₄ < 1
                                                                                                     ==> i₄ < 10000))
                                                                                            && (forall res₄₈: int, i₄₉: int ::
                                                                                                  (  true
                                                                                                    && 1 <= i₄₉
                                                                                                    && i₄₉ <= 10000
                                                                                                    && (forall i₄: int ::
                                                                                                          (  i₄ <= i₄
                                                                                                            && 1 <= i₄
                                                                                                            && i₄ < i₄₉
                                                                                                             ==> i₄ < 10000))
                                                                                                     ==> (i₄₉ < 10000
                                                                                                         ==> true
                                                                                                          && 1 <= i₄₉ + 1
                                                                                                          && i₄₉ + 1 <= 10000
                                                                                                          && (forall i₄: int ::
                                                                                                                (  i₄ <= i₄
                                                                                                                  && 1 <= i₄
                                                                                                                  && i₄ < i₄₉ + 1
                                                                                                                   ==> i₄ < 10000))
                                                                                                          && true
                                                                                                          && (true
                                                                                                             ==> true))
                                                                                                      && (!(i₄₉ < 10000
                                                                                                      )
                                                                                                         ==> true
                                                                                                          && (true
                                                                                                             ==> (  res₃₃ != res₃₉
                                                                                                                || res₃₃ != res₄₈
                                                                                                                 ==> false
                                                                                                                  && (true
                                                                                                                     ==> true))
                                                                                                              && (!(  res₃₃ != res₃₉
                                                                                                                || res₃₃ != res₄₈
                                                                                                              )
                                                                                                                 ==> true)))))))))))))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall SIZE₂₅: int ::
          (true
             ==> (1 < SIZE₂₅
                 ==> (forall a: [int]int ::
                        true
                        && 0 <= 0
                        && 0 <= SIZE₂₅
                        && (forall x₆: int ::
                              ((exists i₅: int ::
                                      x₆ == i₅
                                      && 0 <= i₅
                                      && i₅ < 0)
                                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                        i₅ < SIZE₂₅
                                        && x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < 0
                                        && a[x₆] == __VERIFIER_nondet_short₁₄)))
                        && (forall x₆: int ::
                              (!((exists i₅: int ::
                                      x₆ == i₅
                                      && 0 <= i₅
                                      && i₅ < 0)
                              )
                                 ==> a[x₆] == a[x₆]))
                        && (forall i₅: int ::
                              (  i₅ <= i₅
                                && 0 <= i₅
                                && i₅ < 0
                                 ==> i₅ < SIZE₂₅))
                        && (forall a₂₇: [int]int, i₂₈: int ::
                              (  true
                                && 0 <= i₂₈
                                && i₂₈ <= SIZE₂₅
                                && (forall x₆: int ::
                                      ((exists i₅: int ::
                                              x₆ == i₅
                                              && 0 <= i₅
                                              && i₅ < i₂₈)
                                         ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                                i₅ < SIZE₂₅
                                                && x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₈
                                                && a₂₇[x₆] == __VERIFIER_nondet_short₁₄)))
                                && (forall x₆: int ::
                                      (!((exists i₅: int ::
                                              x₆ == i₅
                                              && 0 <= i₅
                                              && i₅ < i₂₈)
                                      )
                                         ==> a₂₇[x₆] == a[x₆]))
                                && (forall i₅: int ::
                                      (  i₅ <= i₅
                                        && 0 <= i₅
                                        && i₅ < i₂₈
                                         ==> i₅ < SIZE₂₅))
                                 ==> (i₂₈ < SIZE₂₅
                                     ==> (forall __VERIFIER_nondet_short₁: int ::
                                            true
                                            && 0 <= i₂₈ + 1
                                            && i₂₈ + 1 <= SIZE₂₅
                                            && (forall x₆: int ::
                                                  ((exists i₅: int ::
                                                          x₆ == i₅
                                                          && 0 <= i₅
                                                          && i₅ < i₂₈ + 1)
                                                     ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                                            i₅ < SIZE₂₅
                                                            && x₆ == i₅
                                                            && 0 <= i₅
                                                            && i₅ < i₂₈ + 1
                                                            && a₂₇[i₂₈ := __VERIFIER_nondet_short₁][x₆] == __VERIFIER_nondet_short₁₄)))
                                            && (forall x₆: int ::
                                                  (!((exists i₅: int ::
                                                          x₆ == i₅
                                                          && 0 <= i₅
                                                          && i₅ < i₂₈ + 1)
                                                  )
                                                     ==> a₂₇[i₂₈ := __VERIFIER_nondet_short₁][x₆] == a[x₆]))
                                            && (forall i₅: int ::
                                                  (  i₅ <= i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₂₈ + 1
                                                     ==> i₅ < SIZE₂₅))
                                            && true
                                            && (true
                                               ==> true)))
                                  && (!(i₂₈ < SIZE₂₅
                                  )
                                     ==> true
                                      && (true
                                         ==> true
                                          && 0 <= 0
                                          && 0 <= SIZE₂₅
                                          && (forall i₁₀: int ::
                                                (  i₁₀ <= i₁₀
                                                  && 0 <= i₁₀
                                                  && i₁₀ < 0
                                                   ==> i₁₀ < SIZE₂₅))
                                          && (forall i₃₀: int ::
                                                (  true
                                                  && 0 <= i₃₀
                                                  && i₃₀ <= SIZE₂₅
                                                  && (forall i₁₀: int ::
                                                        (  i₁₀ <= i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < i₃₀
                                                           ==> i₁₀ < SIZE₂₅))
                                                   ==> (i₃₀ < SIZE₂₅
                                                       ==> true
                                                        && 0 <= i₃₀ + 1
                                                        && i₃₀ + 1 <= SIZE₂₅
                                                        && (forall i₁₀: int ::
                                                              (  i₁₀ <= i₁₀
                                                                && 0 <= i₁₀
                                                                && i₁₀ < i₃₀ + 1
                                                                 ==> i₁₀ < SIZE₂₅))
                                                        && true
                                                        && (true
                                                           ==> true))
                                                    && (!(i₃₀ < SIZE₂₅
                                                    )
                                                       ==> true
                                                        && (true
                                                           ==> true
                                                            && 0 <= 0
                                                            && 0 <= SIZE₂₅
                                                            && (forall i₁₄: int ::
                                                                  (  i₁₄ <= i₁₄
                                                                    && 0 <= i₁₄
                                                                    && i₁₄ < 0
                                                                     ==> i₁₄ < SIZE₂₅))
                                                            && (forall i₃₂: int ::
                                                                  (  true
                                                                    && 0 <= i₃₂
                                                                    && i₃₂ <= SIZE₂₅
                                                                    && (forall i₁₄: int ::
                                                                          (  i₁₄ <= i₁₄
                                                                            && 0 <= i₁₄
                                                                            && i₁₄ < i₃₂
                                                                             ==> i₁₄ < SIZE₂₅))
                                                                     ==> (i₃₂ < SIZE₂₅
                                                                         ==> true
                                                                          && 0 <= i₃₂ + 1
                                                                          && i₃₂ + 1 <= SIZE₂₅
                                                                          && (forall i₁₄: int ::
                                                                                (  i₁₄ <= i₁₄
                                                                                  && 0 <= i₁₄
                                                                                  && i₁₄ < i₃₂ + 1
                                                                                   ==> i₁₄ < SIZE₂₅))
                                                                          && true
                                                                          && (true
                                                                             ==> true))
                                                                      && (!(i₃₂ < SIZE₂₅
                                                                      )
                                                                         ==> true
                                                                          && (true
                                                                             ==> true
                                                                              && 0 <= 0
                                                                              && 0 <= SIZE₂₅
                                                                              && (forall i₁₈: int ::
                                                                                    (  i₁₈ <= i₁₈
                                                                                      && 0 <= i₁₈
                                                                                      && i₁₈ < 0
                                                                                       ==> i₁₈ < SIZE₂₅))
                                                                              && (forall i₃₄: int ::
                                                                                    (  true
                                                                                      && 0 <= i₃₄
                                                                                      && i₃₄ <= SIZE₂₅
                                                                                      && (forall i₁₈: int ::
                                                                                            (  i₁₈ <= i₁₈
                                                                                              && 0 <= i₁₈
                                                                                              && i₁₈ < i₃₄
                                                                                               ==> i₁₈ < SIZE₂₅))
                                                                                       ==> (i₃₄ < SIZE₂₅
                                                                                           ==> true
                                                                                            && 0 <= i₃₄ + 1
                                                                                            && i₃₄ + 1 <= SIZE₂₅
                                                                                            && (forall i₁₈: int ::
                                                                                                  (  i₁₈ <= i₁₈
                                                                                                    && 0 <= i₁₈
                                                                                                    && i₁₈ < i₃₄ + 1
                                                                                                     ==> i₁₈ < SIZE₂₅))
                                                                                            && true
                                                                                            && (true
                                                                                               ==> true))
                                                                                        && (!(i₃₄ < SIZE₂₅
                                                                                        )
                                                                                           ==> true
                                                                                            && (true
                                                                                               ==> true
                                                                                                && 0 <= 0
                                                                                                && 0 <= SIZE₂₅
                                                                                                && (forall i₂₂: int ::
                                                                                                      (  i₂₂ <= i₂₂
                                                                                                        && 0 <= i₂₂
                                                                                                        && i₂₂ < 0
                                                                                                         ==> i₂₂ < SIZE₂₅))
                                                                                                && (forall sum₃₅: int, i₃₆: int ::
                                                                                                      (  true
                                                                                                        && 0 <= i₃₆
                                                                                                        && i₃₆ <= SIZE₂₅
                                                                                                        && (forall i₂₂: int ::
                                                                                                              (  i₂₂ <= i₂₂
                                                                                                                && 0 <= i₂₂
                                                                                                                && i₂₂ < i₃₆
                                                                                                                 ==> i₂₂ < SIZE₂₅))
                                                                                                         ==> (i₃₆ < SIZE₂₅
                                                                                                             ==> true
                                                                                                              && 0 <= i₃₆ + 1
                                                                                                              && i₃₆ + 1 <= SIZE₂₅
                                                                                                              && (forall i₂₂: int ::
                                                                                                                    (  i₂₂ <= i₂₂
                                                                                                                      && 0 <= i₂₂
                                                                                                                      && i₂₂ < i₃₆ + 1
                                                                                                                       ==> i₂₂ < SIZE₂₅))
                                                                                                              && true
                                                                                                              && (true
                                                                                                                 ==> true))
                                                                                                          && (!(i₃₆ < SIZE₂₅
                                                                                                          )
                                                                                                             ==> true
                                                                                                              && (true
                                                                                                                 ==> sum₃₅ == 0
                                                                                                                  && (true
                                                                                                                     ==> true)))))))))))))))))))))))
              && (!(1 < SIZE₂₅
              )
                 ==> true))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (true
   ==> true
    && (forall SIZE₁₇: int ::
          (true
             ==> (1 < SIZE₁₇
                 ==> (forall a: [int]int ::
                        true
                        && 0 <= 0
                        && 0 <= SIZE₁₇
                        && (forall x₆: int ::
                              ((exists i₅: int ::
                                      x₆ == i₅
                                      && 0 <= i₅
                                      && i₅ < 0)
                                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                        i₅ < SIZE₁₇
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
                                 ==> i₅ < SIZE₁₇))
                        && (forall a₁₉: [int]int, i₂₀: int ::
                              (  true
                                && 0 <= i₂₀
                                && i₂₀ <= SIZE₁₇
                                && (forall x₆: int ::
                                      ((exists i₅: int ::
                                              x₆ == i₅
                                              && 0 <= i₅
                                              && i₅ < i₂₀)
                                         ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                                i₅ < SIZE₁₇
                                                && x₆ == i₅
                                                && 0 <= i₅
                                                && i₅ < i₂₀
                                                && a₁₉[x₆] == __VERIFIER_nondet_short₁₄)))
                                && (forall x₆: int ::
                                      (!((exists i₅: int ::
                                              x₆ == i₅
                                              && 0 <= i₅
                                              && i₅ < i₂₀)
                                      )
                                         ==> a₁₉[x₆] == a[x₆]))
                                && (forall i₅: int ::
                                      (  i₅ <= i₅
                                        && 0 <= i₅
                                        && i₅ < i₂₀
                                         ==> i₅ < SIZE₁₇))
                                 ==> (i₂₀ < SIZE₁₇
                                     ==> (forall __VERIFIER_nondet_short₁: int ::
                                            true
                                            && 0 <= i₂₀ + 1
                                            && i₂₀ + 1 <= SIZE₁₇
                                            && (forall x₆: int ::
                                                  ((exists i₅: int ::
                                                          x₆ == i₅
                                                          && 0 <= i₅
                                                          && i₅ < i₂₀ + 1)
                                                     ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                                            i₅ < SIZE₁₇
                                                            && x₆ == i₅
                                                            && 0 <= i₅
                                                            && i₅ < i₂₀ + 1
                                                            && a₁₉[i₂₀ := __VERIFIER_nondet_short₁][x₆] == __VERIFIER_nondet_short₁₄)))
                                            && (forall x₆: int ::
                                                  (!((exists i₅: int ::
                                                          x₆ == i₅
                                                          && 0 <= i₅
                                                          && i₅ < i₂₀ + 1)
                                                  )
                                                     ==> a₁₉[i₂₀ := __VERIFIER_nondet_short₁][x₆] == a[x₆]))
                                            && (forall i₅: int ::
                                                  (  i₅ <= i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₂₀ + 1
                                                     ==> i₅ < SIZE₁₇))
                                            && true
                                            && (true
                                               ==> true)))
                                  && (!(i₂₀ < SIZE₁₇
                                  )
                                     ==> true
                                      && (true
                                         ==> true
                                          && 0 <= 0
                                          && 0 <= SIZE₁₇
                                          && (forall i₁₀: int ::
                                                (  i₁₀ <= i₁₀
                                                  && 0 <= i₁₀
                                                  && i₁₀ < 0
                                                   ==> i₁₀ < SIZE₁₇))
                                          && (forall i₂₂: int ::
                                                (  true
                                                  && 0 <= i₂₂
                                                  && i₂₂ <= SIZE₁₇
                                                  && (forall i₁₀: int ::
                                                        (  i₁₀ <= i₁₀
                                                          && 0 <= i₁₀
                                                          && i₁₀ < i₂₂
                                                           ==> i₁₀ < SIZE₁₇))
                                                   ==> (i₂₂ < SIZE₁₇
                                                       ==> true
                                                        && 0 <= i₂₂ + 1
                                                        && i₂₂ + 1 <= SIZE₁₇
                                                        && (forall i₁₀: int ::
                                                              (  i₁₀ <= i₁₀
                                                                && 0 <= i₁₀
                                                                && i₁₀ < i₂₂ + 1
                                                                 ==> i₁₀ < SIZE₁₇))
                                                        && true
                                                        && (true
                                                           ==> true))
                                                    && (!(i₂₂ < SIZE₁₇
                                                    )
                                                       ==> true
                                                        && (true
                                                           ==> true
                                                            && 0 <= 0
                                                            && 0 <= SIZE₁₇
                                                            && (forall i₁₄: int ::
                                                                  (  i₁₄ <= i₁₄
                                                                    && 0 <= i₁₄
                                                                    && i₁₄ < 0
                                                                     ==> i₁₄ < SIZE₁₇))
                                                            && (forall sum₂₃: int, i₂₄: int ::
                                                                  (  true
                                                                    && 0 <= i₂₄
                                                                    && i₂₄ <= SIZE₁₇
                                                                    && (forall i₁₄: int ::
                                                                          (  i₁₄ <= i₁₄
                                                                            && 0 <= i₁₄
                                                                            && i₁₄ < i₂₄
                                                                             ==> i₁₄ < SIZE₁₇))
                                                                     ==> (i₂₄ < SIZE₁₇
                                                                         ==> true
                                                                          && 0 <= i₂₄ + 1
                                                                          && i₂₄ + 1 <= SIZE₁₇
                                                                          && (forall i₁₄: int ::
                                                                                (  i₁₄ <= i₁₄
                                                                                  && 0 <= i₁₄
                                                                                  && i₁₄ < i₂₄ + 1
                                                                                   ==> i₁₄ < SIZE₁₇))
                                                                          && true
                                                                          && (true
                                                                             ==> true))
                                                                      && (!(i₂₄ < SIZE₁₇
                                                                      )
                                                                         ==> true
                                                                          && (true
                                                                             ==> sum₂₃ == 0
                                                                              && (true
                                                                                 ==> true)))))))))))))))
              && (!(1 < SIZE₁₇
              )
                 ==> true))));


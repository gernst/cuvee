data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall SIZE₂₅: int ::
      (forall a: [int]int ::
            (1 < SIZE₂₅
               ==> 0 <= 0
                && 0 <= SIZE₂₅
                && (forall x₆: int, i₅: int ::
                      (  x₆ == i₅
                        && 0 <= i₅
                        && i₅ < 0
                         ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                i₅ < SIZE₂₅
                                && x₆ == i₅
                                && 0 <= i₅
                                && i₅ < 0
                                && a[x₆] == __VERIFIER_nondet_short₁₄)))
                && (forall x₆: int ::
                        (exists i₅: int ::
                                x₆ == i₅
                                && 0 <= i₅
                                && i₅ < 0)
                        || a[x₆] == a[x₆])
                && (forall i₅: int ::
                      (  0 <= i₅
                        && i₅ < 0
                         ==> i₅ < SIZE₂₅))
                && (forall a₂₇: [int]int, i₂₈: int ::
                      (  0 <= i₂₈
                        && i₂₈ <= SIZE₂₅
                        && (forall x₆: int, i₅: int ::
                              (  x₆ == i₅
                                && 0 <= i₅
                                && i₅ < i₂₈
                                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                        i₅ < SIZE₂₅
                                        && x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₂₈
                                        && a₂₇[x₆] == __VERIFIER_nondet_short₁₄)))
                        && (forall x₆: int ::
                                (exists i₅: int ::
                                        x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₂₈)
                                || a₂₇[x₆] == a[x₆])
                        && (forall i₅: int ::
                              (  0 <= i₅
                                && i₅ < i₂₈
                                 ==> i₅ < SIZE₂₅))
                         ==> (forall __VERIFIER_nondet_short₁: int ::
                                (i₂₈ < SIZE₂₅
                                   ==> 0 <= i₂₈ + 1
                                    && i₂₈ + 1 <= SIZE₂₅
                                    && (forall x₆: int, i₅: int ::
                                          (  x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₂₈ + 1
                                             ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                                    i₅ < SIZE₂₅
                                                    && x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₂₈ + 1
                                                    && a₂₇[i₂₈ := __VERIFIER_nondet_short₁][x₆] == __VERIFIER_nondet_short₁₄)))
                                    && (forall x₆: int ::
                                            (exists i₅: int ::
                                                    x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₂₈ + 1)
                                            || a₂₇[i₂₈ := __VERIFIER_nondet_short₁][x₆] == a[x₆])
                                    && (forall i₅: int ::
                                          (  0 <= i₅
                                            && i₅ < i₂₈ + 1
                                             ==> i₅ < SIZE₂₅))))
                          &&   i₂₈ < SIZE₂₅
                            ||   0 <= 0
                              && 0 <= SIZE₂₅
                              && (forall i₁₀: int ::
                                    (  0 <= i₁₀
                                      && i₁₀ < 0
                                       ==> i₁₀ < SIZE₂₅))
                              && (forall i₃₀: int ::
                                    (  0 <= i₃₀
                                      && i₃₀ <= SIZE₂₅
                                      && (forall i₁₀: int ::
                                            (  0 <= i₁₀
                                              && i₁₀ < i₃₀
                                               ==> i₁₀ < SIZE₂₅))
                                       ==> (i₃₀ < SIZE₂₅
                                           ==> 0 <= i₃₀ + 1
                                            && i₃₀ + 1 <= SIZE₂₅
                                            && (forall i₁₀: int ::
                                                  (  0 <= i₁₀
                                                    && i₁₀ < i₃₀ + 1
                                                     ==> i₁₀ < SIZE₂₅)))
                                        &&   i₃₀ < SIZE₂₅
                                          ||   0 <= 0
                                            && 0 <= SIZE₂₅
                                            && (forall i₁₄: int ::
                                                  (  0 <= i₁₄
                                                    && i₁₄ < 0
                                                     ==> i₁₄ < SIZE₂₅))
                                            && (forall i₃₂: int ::
                                                  (  0 <= i₃₂
                                                    && i₃₂ <= SIZE₂₅
                                                    && (forall i₁₄: int ::
                                                          (  0 <= i₁₄
                                                            && i₁₄ < i₃₂
                                                             ==> i₁₄ < SIZE₂₅))
                                                     ==> (i₃₂ < SIZE₂₅
                                                         ==> 0 <= i₃₂ + 1
                                                          && i₃₂ + 1 <= SIZE₂₅
                                                          && (forall i₁₄: int ::
                                                                (  0 <= i₁₄
                                                                  && i₁₄ < i₃₂ + 1
                                                                   ==> i₁₄ < SIZE₂₅)))
                                                      &&   i₃₂ < SIZE₂₅
                                                        ||   0 <= 0
                                                          && 0 <= SIZE₂₅
                                                          && (forall i₁₈: int ::
                                                                (  0 <= i₁₈
                                                                  && i₁₈ < 0
                                                                   ==> i₁₈ < SIZE₂₅))
                                                          && (forall i₃₄: int ::
                                                                (  0 <= i₃₄
                                                                  && i₃₄ <= SIZE₂₅
                                                                  && (forall i₁₈: int ::
                                                                        (  0 <= i₁₈
                                                                          && i₁₈ < i₃₄
                                                                           ==> i₁₈ < SIZE₂₅))
                                                                   ==> (i₃₄ < SIZE₂₅
                                                                       ==> 0 <= i₃₄ + 1
                                                                        && i₃₄ + 1 <= SIZE₂₅
                                                                        && (forall i₁₈: int ::
                                                                              (  0 <= i₁₈
                                                                                && i₁₈ < i₃₄ + 1
                                                                                 ==> i₁₈ < SIZE₂₅)))
                                                                    &&   i₃₄ < SIZE₂₅
                                                                      ||   0 <= 0
                                                                        && 0 <= SIZE₂₅
                                                                        && (forall i₂₂: int ::
                                                                              (  0 <= i₂₂
                                                                                && i₂₂ < 0
                                                                                 ==> i₂₂ < SIZE₂₅))
                                                                        && (forall sum₃₅: int, i₃₆: int ::
                                                                              (  0 <= i₃₆
                                                                                && i₃₆ <= SIZE₂₅
                                                                                && (forall i₂₂: int ::
                                                                                      (  0 <= i₂₂
                                                                                        && i₂₂ < i₃₆
                                                                                         ==> i₂₂ < SIZE₂₅))
                                                                                 ==> (i₃₆ < SIZE₂₅
                                                                                     ==> 0 <= i₃₆ + 1
                                                                                      && i₃₆ + 1 <= SIZE₂₅
                                                                                      && (forall i₂₂: int ::
                                                                                            (  0 <= i₂₂
                                                                                              && i₂₂ < i₃₆ + 1
                                                                                               ==> i₂₂ < SIZE₂₅)))
                                                                                  &&   i₃₆ < SIZE₂₅
                                                                                    || sum₃₅ == 0)))))))))))));


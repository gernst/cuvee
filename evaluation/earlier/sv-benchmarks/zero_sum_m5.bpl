data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall SIZE₄₉: int ::
      (forall a: [int]int ::
            (1 < SIZE₄₉
               ==> 0 <= 0
                && 0 <= SIZE₄₉
                && (forall x₆: int, i₅: int ::
                      (  x₆ == i₅
                        && 0 <= i₅
                        && i₅ < 0
                         ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                i₅ < SIZE₄₉
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
                         ==> i₅ < SIZE₄₉))
                && (forall a₅₁: [int]int, i₅₂: int ::
                      (  0 <= i₅₂
                        && i₅₂ <= SIZE₄₉
                        && (forall x₆: int, i₅: int ::
                              (  x₆ == i₅
                                && 0 <= i₅
                                && i₅ < i₅₂
                                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                        i₅ < SIZE₄₉
                                        && x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₅₂
                                        && a₅₁[x₆] == __VERIFIER_nondet_short₁₄)))
                        && (forall x₆: int ::
                                (exists i₅: int ::
                                        x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₅₂)
                                || a₅₁[x₆] == a[x₆])
                        && (forall i₅: int ::
                              (  0 <= i₅
                                && i₅ < i₅₂
                                 ==> i₅ < SIZE₄₉))
                         ==> (forall __VERIFIER_nondet_short₁: int ::
                                (i₅₂ < SIZE₄₉
                                   ==> 0 <= i₅₂ + 1
                                    && i₅₂ + 1 <= SIZE₄₉
                                    && (forall x₆: int, i₅: int ::
                                          (  x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₅₂ + 1
                                             ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                                    i₅ < SIZE₄₉
                                                    && x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₅₂ + 1
                                                    && a₅₁[i₅₂ := __VERIFIER_nondet_short₁][x₆] == __VERIFIER_nondet_short₁₄)))
                                    && (forall x₆: int ::
                                            (exists i₅: int ::
                                                    x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₅₂ + 1)
                                            || a₅₁[i₅₂ := __VERIFIER_nondet_short₁][x₆] == a[x₆])
                                    && (forall i₅: int ::
                                          (  0 <= i₅
                                            && i₅ < i₅₂ + 1
                                             ==> i₅ < SIZE₄₉))))
                          &&   i₅₂ < SIZE₄₉
                            ||   0 <= 0
                              && 0 <= SIZE₄₉
                              && (forall i₁₀: int ::
                                    (  0 <= i₁₀
                                      && i₁₀ < 0
                                       ==> i₁₀ < SIZE₄₉))
                              && (forall i₅₄: int ::
                                    (  0 <= i₅₄
                                      && i₅₄ <= SIZE₄₉
                                      && (forall i₁₀: int ::
                                            (  0 <= i₁₀
                                              && i₁₀ < i₅₄
                                               ==> i₁₀ < SIZE₄₉))
                                       ==> (i₅₄ < SIZE₄₉
                                           ==> 0 <= i₅₄ + 1
                                            && i₅₄ + 1 <= SIZE₄₉
                                            && (forall i₁₀: int ::
                                                  (  0 <= i₁₀
                                                    && i₁₀ < i₅₄ + 1
                                                     ==> i₁₀ < SIZE₄₉)))
                                        &&   i₅₄ < SIZE₄₉
                                          ||   0 <= 0
                                            && 0 <= SIZE₄₉
                                            && (forall i₁₄: int ::
                                                  (  0 <= i₁₄
                                                    && i₁₄ < 0
                                                     ==> i₁₄ < SIZE₄₉))
                                            && (forall i₅₆: int ::
                                                  (  0 <= i₅₆
                                                    && i₅₆ <= SIZE₄₉
                                                    && (forall i₁₄: int ::
                                                          (  0 <= i₁₄
                                                            && i₁₄ < i₅₆
                                                             ==> i₁₄ < SIZE₄₉))
                                                     ==> (i₅₆ < SIZE₄₉
                                                         ==> 0 <= i₅₆ + 1
                                                          && i₅₆ + 1 <= SIZE₄₉
                                                          && (forall i₁₄: int ::
                                                                (  0 <= i₁₄
                                                                  && i₁₄ < i₅₆ + 1
                                                                   ==> i₁₄ < SIZE₄₉)))
                                                      &&   i₅₆ < SIZE₄₉
                                                        ||   0 <= 0
                                                          && 0 <= SIZE₄₉
                                                          && (forall i₁₈: int ::
                                                                (  0 <= i₁₈
                                                                  && i₁₈ < 0
                                                                   ==> i₁₈ < SIZE₄₉))
                                                          && (forall i₅₈: int ::
                                                                (  0 <= i₅₈
                                                                  && i₅₈ <= SIZE₄₉
                                                                  && (forall i₁₈: int ::
                                                                        (  0 <= i₁₈
                                                                          && i₁₈ < i₅₈
                                                                           ==> i₁₈ < SIZE₄₉))
                                                                   ==> (i₅₈ < SIZE₄₉
                                                                       ==> 0 <= i₅₈ + 1
                                                                        && i₅₈ + 1 <= SIZE₄₉
                                                                        && (forall i₁₈: int ::
                                                                              (  0 <= i₁₈
                                                                                && i₁₈ < i₅₈ + 1
                                                                                 ==> i₁₈ < SIZE₄₉)))
                                                                    &&   i₅₈ < SIZE₄₉
                                                                      ||   0 <= 0
                                                                        && 0 <= SIZE₄₉
                                                                        && (forall i₂₂: int ::
                                                                              (  0 <= i₂₂
                                                                                && i₂₂ < 0
                                                                                 ==> i₂₂ < SIZE₄₉))
                                                                        && (forall i₆₀: int ::
                                                                              (  0 <= i₆₀
                                                                                && i₆₀ <= SIZE₄₉
                                                                                && (forall i₂₂: int ::
                                                                                      (  0 <= i₂₂
                                                                                        && i₂₂ < i₆₀
                                                                                         ==> i₂₂ < SIZE₄₉))
                                                                                 ==> (i₆₀ < SIZE₄₉
                                                                                     ==> 0 <= i₆₀ + 1
                                                                                      && i₆₀ + 1 <= SIZE₄₉
                                                                                      && (forall i₂₂: int ::
                                                                                            (  0 <= i₂₂
                                                                                              && i₂₂ < i₆₀ + 1
                                                                                               ==> i₂₂ < SIZE₄₉)))
                                                                                  &&   i₆₀ < SIZE₄₉
                                                                                    ||   0 <= 0
                                                                                      && 0 <= SIZE₄₉
                                                                                      && (forall i₂₆: int ::
                                                                                            (  0 <= i₂₆
                                                                                              && i₂₆ < 0
                                                                                               ==> i₂₆ < SIZE₄₉))
                                                                                      && (forall i₆₂: int ::
                                                                                            (  0 <= i₆₂
                                                                                              && i₆₂ <= SIZE₄₉
                                                                                              && (forall i₂₆: int ::
                                                                                                    (  0 <= i₂₆
                                                                                                      && i₂₆ < i₆₂
                                                                                                       ==> i₂₆ < SIZE₄₉))
                                                                                               ==> (i₆₂ < SIZE₄₉
                                                                                                   ==> 0 <= i₆₂ + 1
                                                                                                    && i₆₂ + 1 <= SIZE₄₉
                                                                                                    && (forall i₂₆: int ::
                                                                                                          (  0 <= i₂₆
                                                                                                            && i₂₆ < i₆₂ + 1
                                                                                                             ==> i₂₆ < SIZE₄₉)))
                                                                                                &&   i₆₂ < SIZE₄₉
                                                                                                  ||   0 <= 0
                                                                                                    && 0 <= SIZE₄₉
                                                                                                    && (forall i₃₀: int ::
                                                                                                          (  0 <= i₃₀
                                                                                                            && i₃₀ < 0
                                                                                                             ==> i₃₀ < SIZE₄₉))
                                                                                                    && (forall i₆₄: int ::
                                                                                                          (  0 <= i₆₄
                                                                                                            && i₆₄ <= SIZE₄₉
                                                                                                            && (forall i₃₀: int ::
                                                                                                                  (  0 <= i₃₀
                                                                                                                    && i₃₀ < i₆₄
                                                                                                                     ==> i₃₀ < SIZE₄₉))
                                                                                                             ==> (i₆₄ < SIZE₄₉
                                                                                                                 ==> 0 <= i₆₄ + 1
                                                                                                                  && i₆₄ + 1 <= SIZE₄₉
                                                                                                                  && (forall i₃₀: int ::
                                                                                                                        (  0 <= i₃₀
                                                                                                                          && i₃₀ < i₆₄ + 1
                                                                                                                           ==> i₃₀ < SIZE₄₉)))
                                                                                                              &&   i₆₄ < SIZE₄₉
                                                                                                                ||   0 <= 0
                                                                                                                  && 0 <= SIZE₄₉
                                                                                                                  && (forall i₃₄: int ::
                                                                                                                        (  0 <= i₃₄
                                                                                                                          && i₃₄ < 0
                                                                                                                           ==> i₃₄ < SIZE₄₉))
                                                                                                                  && (forall i₆₆: int ::
                                                                                                                        (  0 <= i₆₆
                                                                                                                          && i₆₆ <= SIZE₄₉
                                                                                                                          && (forall i₃₄: int ::
                                                                                                                                (  0 <= i₃₄
                                                                                                                                  && i₃₄ < i₆₆
                                                                                                                                   ==> i₃₄ < SIZE₄₉))
                                                                                                                           ==> (i₆₆ < SIZE₄₉
                                                                                                                               ==> 0 <= i₆₆ + 1
                                                                                                                                && i₆₆ + 1 <= SIZE₄₉
                                                                                                                                && (forall i₃₄: int ::
                                                                                                                                      (  0 <= i₃₄
                                                                                                                                        && i₃₄ < i₆₆ + 1
                                                                                                                                         ==> i₃₄ < SIZE₄₉)))
                                                                                                                            &&   i₆₆ < SIZE₄₉
                                                                                                                              ||   0 <= 0
                                                                                                                                && 0 <= SIZE₄₉
                                                                                                                                && (forall i₃₈: int ::
                                                                                                                                      (  0 <= i₃₈
                                                                                                                                        && i₃₈ < 0
                                                                                                                                         ==> i₃₈ < SIZE₄₉))
                                                                                                                                && (forall i₆₈: int ::
                                                                                                                                      (  0 <= i₆₈
                                                                                                                                        && i₆₈ <= SIZE₄₉
                                                                                                                                        && (forall i₃₈: int ::
                                                                                                                                              (  0 <= i₃₈
                                                                                                                                                && i₃₈ < i₆₈
                                                                                                                                                 ==> i₃₈ < SIZE₄₉))
                                                                                                                                         ==> (i₆₈ < SIZE₄₉
                                                                                                                                             ==> 0 <= i₆₈ + 1
                                                                                                                                              && i₆₈ + 1 <= SIZE₄₉
                                                                                                                                              && (forall i₃₈: int ::
                                                                                                                                                    (  0 <= i₃₈
                                                                                                                                                      && i₃₈ < i₆₈ + 1
                                                                                                                                                       ==> i₃₈ < SIZE₄₉)))
                                                                                                                                          &&   i₆₈ < SIZE₄₉
                                                                                                                                            ||   0 <= 0
                                                                                                                                              && 0 <= SIZE₄₉
                                                                                                                                              && (forall i₄₂: int ::
                                                                                                                                                    (  0 <= i₄₂
                                                                                                                                                      && i₄₂ < 0
                                                                                                                                                       ==> i₄₂ < SIZE₄₉))
                                                                                                                                              && (forall i₇₀: int ::
                                                                                                                                                    (  0 <= i₇₀
                                                                                                                                                      && i₇₀ <= SIZE₄₉
                                                                                                                                                      && (forall i₄₂: int ::
                                                                                                                                                            (  0 <= i₄₂
                                                                                                                                                              && i₄₂ < i₇₀
                                                                                                                                                               ==> i₄₂ < SIZE₄₉))
                                                                                                                                                       ==> (i₇₀ < SIZE₄₉
                                                                                                                                                           ==> 0 <= i₇₀ + 1
                                                                                                                                                            && i₇₀ + 1 <= SIZE₄₉
                                                                                                                                                            && (forall i₄₂: int ::
                                                                                                                                                                  (  0 <= i₄₂
                                                                                                                                                                    && i₄₂ < i₇₀ + 1
                                                                                                                                                                     ==> i₄₂ < SIZE₄₉)))
                                                                                                                                                        &&   i₇₀ < SIZE₄₉
                                                                                                                                                          ||   0 <= 0
                                                                                                                                                            && 0 <= SIZE₄₉
                                                                                                                                                            && (forall i₄₆: int ::
                                                                                                                                                                  (  0 <= i₄₆
                                                                                                                                                                    && i₄₆ < 0
                                                                                                                                                                     ==> i₄₆ < SIZE₄₉))
                                                                                                                                                            && (forall sum₇₁: int, i₇₂: int ::
                                                                                                                                                                  (  0 <= i₇₂
                                                                                                                                                                    && i₇₂ <= SIZE₄₉
                                                                                                                                                                    && (forall i₄₆: int ::
                                                                                                                                                                          (  0 <= i₄₆
                                                                                                                                                                            && i₄₆ < i₇₂
                                                                                                                                                                             ==> i₄₆ < SIZE₄₉))
                                                                                                                                                                     ==> (i₇₂ < SIZE₄₉
                                                                                                                                                                         ==> 0 <= i₇₂ + 1
                                                                                                                                                                          && i₇₂ + 1 <= SIZE₄₉
                                                                                                                                                                          && (forall i₄₆: int ::
                                                                                                                                                                                (  0 <= i₄₆
                                                                                                                                                                                  && i₄₆ < i₇₂ + 1
                                                                                                                                                                                   ==> i₄₆ < SIZE₄₉)))
                                                                                                                                                                      &&   i₇₂ < SIZE₄₉
                                                                                                                                                                        || sum₇₁ == 0)))))))))))))))))))))))));


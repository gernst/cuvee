data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var SIZE: int;

goal (forall SIZE₃₃: int ::
      (forall a: [int]int ::
            (1 < SIZE₃₃
               ==> 0 <= 0
                && 0 <= SIZE₃₃
                && (forall x₆: int, i₅: int ::
                      (  x₆ == i₅
                        && 0 <= i₅
                        && i₅ < 0
                         ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                i₅ < SIZE₃₃
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
                         ==> i₅ < SIZE₃₃))
                && (forall a₃₅: [int]int, i₃₆: int ::
                      (  0 <= i₃₆
                        && i₃₆ <= SIZE₃₃
                        && (forall x₆: int, i₅: int ::
                              (  x₆ == i₅
                                && 0 <= i₅
                                && i₅ < i₃₆
                                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                        i₅ < SIZE₃₃
                                        && x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₃₆
                                        && a₃₅[x₆] == __VERIFIER_nondet_short₁₄)))
                        && (forall x₆: int ::
                                (exists i₅: int ::
                                        x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₃₆)
                                || a₃₅[x₆] == a[x₆])
                        && (forall i₅: int ::
                              (  0 <= i₅
                                && i₅ < i₃₆
                                 ==> i₅ < SIZE₃₃))
                         ==> (forall __VERIFIER_nondet_short₁: int ::
                                (i₃₆ < SIZE₃₃
                                   ==> 0 <= i₃₆ + 1
                                    && i₃₆ + 1 <= SIZE₃₃
                                    && (forall x₆: int, i₅: int ::
                                          (  x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₃₆ + 1
                                             ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                                    i₅ < SIZE₃₃
                                                    && x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₃₆ + 1
                                                    && a₃₅[i₃₆ := __VERIFIER_nondet_short₁][x₆] == __VERIFIER_nondet_short₁₄)))
                                    && (forall x₆: int ::
                                            (exists i₅: int ::
                                                    x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₃₆ + 1)
                                            || a₃₅[i₃₆ := __VERIFIER_nondet_short₁][x₆] == a[x₆])
                                    && (forall i₅: int ::
                                          (  0 <= i₅
                                            && i₅ < i₃₆ + 1
                                             ==> i₅ < SIZE₃₃))))
                          &&   i₃₆ < SIZE₃₃
                            ||   0 <= 0
                              && 0 <= SIZE₃₃
                              && (forall i₁₀: int ::
                                    (  0 <= i₁₀
                                      && i₁₀ < 0
                                       ==> i₁₀ < SIZE₃₃))
                              && (forall i₃₈: int ::
                                    (  0 <= i₃₈
                                      && i₃₈ <= SIZE₃₃
                                      && (forall i₁₀: int ::
                                            (  0 <= i₁₀
                                              && i₁₀ < i₃₈
                                               ==> i₁₀ < SIZE₃₃))
                                       ==> (i₃₈ < SIZE₃₃
                                           ==> 0 <= i₃₈ + 1
                                            && i₃₈ + 1 <= SIZE₃₃
                                            && (forall i₁₀: int ::
                                                  (  0 <= i₁₀
                                                    && i₁₀ < i₃₈ + 1
                                                     ==> i₁₀ < SIZE₃₃)))
                                        &&   i₃₈ < SIZE₃₃
                                          ||   0 <= 0
                                            && 0 <= SIZE₃₃
                                            && (forall i₁₄: int ::
                                                  (  0 <= i₁₄
                                                    && i₁₄ < 0
                                                     ==> i₁₄ < SIZE₃₃))
                                            && (forall i₄₀: int ::
                                                  (  0 <= i₄₀
                                                    && i₄₀ <= SIZE₃₃
                                                    && (forall i₁₄: int ::
                                                          (  0 <= i₁₄
                                                            && i₁₄ < i₄₀
                                                             ==> i₁₄ < SIZE₃₃))
                                                     ==> (i₄₀ < SIZE₃₃
                                                         ==> 0 <= i₄₀ + 1
                                                          && i₄₀ + 1 <= SIZE₃₃
                                                          && (forall i₁₄: int ::
                                                                (  0 <= i₁₄
                                                                  && i₁₄ < i₄₀ + 1
                                                                   ==> i₁₄ < SIZE₃₃)))
                                                      &&   i₄₀ < SIZE₃₃
                                                        ||   0 <= 0
                                                          && 0 <= SIZE₃₃
                                                          && (forall i₁₈: int ::
                                                                (  0 <= i₁₈
                                                                  && i₁₈ < 0
                                                                   ==> i₁₈ < SIZE₃₃))
                                                          && (forall i₄₂: int ::
                                                                (  0 <= i₄₂
                                                                  && i₄₂ <= SIZE₃₃
                                                                  && (forall i₁₈: int ::
                                                                        (  0 <= i₁₈
                                                                          && i₁₈ < i₄₂
                                                                           ==> i₁₈ < SIZE₃₃))
                                                                   ==> (i₄₂ < SIZE₃₃
                                                                       ==> 0 <= i₄₂ + 1
                                                                        && i₄₂ + 1 <= SIZE₃₃
                                                                        && (forall i₁₈: int ::
                                                                              (  0 <= i₁₈
                                                                                && i₁₈ < i₄₂ + 1
                                                                                 ==> i₁₈ < SIZE₃₃)))
                                                                    &&   i₄₂ < SIZE₃₃
                                                                      ||   0 <= 0
                                                                        && 0 <= SIZE₃₃
                                                                        && (forall i₂₂: int ::
                                                                              (  0 <= i₂₂
                                                                                && i₂₂ < 0
                                                                                 ==> i₂₂ < SIZE₃₃))
                                                                        && (forall i₄₄: int ::
                                                                              (  0 <= i₄₄
                                                                                && i₄₄ <= SIZE₃₃
                                                                                && (forall i₂₂: int ::
                                                                                      (  0 <= i₂₂
                                                                                        && i₂₂ < i₄₄
                                                                                         ==> i₂₂ < SIZE₃₃))
                                                                                 ==> (i₄₄ < SIZE₃₃
                                                                                     ==> 0 <= i₄₄ + 1
                                                                                      && i₄₄ + 1 <= SIZE₃₃
                                                                                      && (forall i₂₂: int ::
                                                                                            (  0 <= i₂₂
                                                                                              && i₂₂ < i₄₄ + 1
                                                                                               ==> i₂₂ < SIZE₃₃)))
                                                                                  &&   i₄₄ < SIZE₃₃
                                                                                    ||   0 <= 0
                                                                                      && 0 <= SIZE₃₃
                                                                                      && (forall i₂₆: int ::
                                                                                            (  0 <= i₂₆
                                                                                              && i₂₆ < 0
                                                                                               ==> i₂₆ < SIZE₃₃))
                                                                                      && (forall i₄₆: int ::
                                                                                            (  0 <= i₄₆
                                                                                              && i₄₆ <= SIZE₃₃
                                                                                              && (forall i₂₆: int ::
                                                                                                    (  0 <= i₂₆
                                                                                                      && i₂₆ < i₄₆
                                                                                                       ==> i₂₆ < SIZE₃₃))
                                                                                               ==> (i₄₆ < SIZE₃₃
                                                                                                   ==> 0 <= i₄₆ + 1
                                                                                                    && i₄₆ + 1 <= SIZE₃₃
                                                                                                    && (forall i₂₆: int ::
                                                                                                          (  0 <= i₂₆
                                                                                                            && i₂₆ < i₄₆ + 1
                                                                                                             ==> i₂₆ < SIZE₃₃)))
                                                                                                &&   i₄₆ < SIZE₃₃
                                                                                                  ||   0 <= 0
                                                                                                    && 0 <= SIZE₃₃
                                                                                                    && (forall i₃₀: int ::
                                                                                                          (  0 <= i₃₀
                                                                                                            && i₃₀ < 0
                                                                                                             ==> i₃₀ < SIZE₃₃))
                                                                                                    && (forall sum₄₇: int, i₄₈: int ::
                                                                                                          (  0 <= i₄₈
                                                                                                            && i₄₈ <= SIZE₃₃
                                                                                                            && (forall i₃₀: int ::
                                                                                                                  (  0 <= i₃₀
                                                                                                                    && i₃₀ < i₄₈
                                                                                                                     ==> i₃₀ < SIZE₃₃))
                                                                                                             ==> (i₄₈ < SIZE₃₃
                                                                                                                 ==> 0 <= i₄₈ + 1
                                                                                                                  && i₄₈ + 1 <= SIZE₃₃
                                                                                                                  && (forall i₃₀: int ::
                                                                                                                        (  0 <= i₃₀
                                                                                                                          && i₃₀ < i₄₈ + 1
                                                                                                                           ==> i₃₀ < SIZE₃₃)))
                                                                                                              &&   i₄₈ < SIZE₃₃
                                                                                                                || sum₄₇ == 0)))))))))))))))));


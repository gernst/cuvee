data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

var SIZE: int;

goal (forall SIZE₄₁: int ::
      (forall a: [int]int ::
            (1 < SIZE₄₁
               ==> 0 <= 0
                && 0 <= SIZE₄₁
                && (forall x₆: int, i₅: int ::
                      (  x₆ == i₅
                        && 0 <= i₅
                        && i₅ < 0
                         ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                i₅ < SIZE₄₁
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
                         ==> i₅ < SIZE₄₁))
                && (forall a₄₃: [int]int, i₄₄: int ::
                      (  0 <= i₄₄
                        && i₄₄ <= SIZE₄₁
                        && (forall x₆: int, i₅: int ::
                              (  x₆ == i₅
                                && 0 <= i₅
                                && i₅ < i₄₄
                                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                        i₅ < SIZE₄₁
                                        && x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₄₄
                                        && a₄₃[x₆] == __VERIFIER_nondet_short₁₄)))
                        && (forall x₆: int ::
                                (exists i₅: int ::
                                        x₆ == i₅
                                        && 0 <= i₅
                                        && i₅ < i₄₄)
                                || a₄₃[x₆] == a[x₆])
                        && (forall i₅: int ::
                              (  0 <= i₅
                                && i₅ < i₄₄
                                 ==> i₅ < SIZE₄₁))
                         ==> (forall __VERIFIER_nondet_short₁: int ::
                                (i₄₄ < SIZE₄₁
                                   ==> 0 <= i₄₄ + 1
                                    && i₄₄ + 1 <= SIZE₄₁
                                    && (forall x₆: int, i₅: int ::
                                          (  x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₄₄ + 1
                                             ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                                                    i₅ < SIZE₄₁
                                                    && x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₄₄ + 1
                                                    && a₄₃[i₄₄ := __VERIFIER_nondet_short₁][x₆] == __VERIFIER_nondet_short₁₄)))
                                    && (forall x₆: int ::
                                            (exists i₅: int ::
                                                    x₆ == i₅
                                                    && 0 <= i₅
                                                    && i₅ < i₄₄ + 1)
                                            || a₄₃[i₄₄ := __VERIFIER_nondet_short₁][x₆] == a[x₆])
                                    && (forall i₅: int ::
                                          (  0 <= i₅
                                            && i₅ < i₄₄ + 1
                                             ==> i₅ < SIZE₄₁))))
                          &&   i₄₄ < SIZE₄₁
                            ||   0 <= 0
                              && 0 <= SIZE₄₁
                              && (forall i₁₀: int ::
                                    (  0 <= i₁₀
                                      && i₁₀ < 0
                                       ==> i₁₀ < SIZE₄₁))
                              && (forall i₄₆: int ::
                                    (  0 <= i₄₆
                                      && i₄₆ <= SIZE₄₁
                                      && (forall i₁₀: int ::
                                            (  0 <= i₁₀
                                              && i₁₀ < i₄₆
                                               ==> i₁₀ < SIZE₄₁))
                                       ==> (i₄₆ < SIZE₄₁
                                           ==> 0 <= i₄₆ + 1
                                            && i₄₆ + 1 <= SIZE₄₁
                                            && (forall i₁₀: int ::
                                                  (  0 <= i₁₀
                                                    && i₁₀ < i₄₆ + 1
                                                     ==> i₁₀ < SIZE₄₁)))
                                        &&   i₄₆ < SIZE₄₁
                                          ||   0 <= 0
                                            && 0 <= SIZE₄₁
                                            && (forall i₁₄: int ::
                                                  (  0 <= i₁₄
                                                    && i₁₄ < 0
                                                     ==> i₁₄ < SIZE₄₁))
                                            && (forall i₄₈: int ::
                                                  (  0 <= i₄₈
                                                    && i₄₈ <= SIZE₄₁
                                                    && (forall i₁₄: int ::
                                                          (  0 <= i₁₄
                                                            && i₁₄ < i₄₈
                                                             ==> i₁₄ < SIZE₄₁))
                                                     ==> (i₄₈ < SIZE₄₁
                                                         ==> 0 <= i₄₈ + 1
                                                          && i₄₈ + 1 <= SIZE₄₁
                                                          && (forall i₁₄: int ::
                                                                (  0 <= i₁₄
                                                                  && i₁₄ < i₄₈ + 1
                                                                   ==> i₁₄ < SIZE₄₁)))
                                                      &&   i₄₈ < SIZE₄₁
                                                        ||   0 <= 0
                                                          && 0 <= SIZE₄₁
                                                          && (forall i₁₈: int ::
                                                                (  0 <= i₁₈
                                                                  && i₁₈ < 0
                                                                   ==> i₁₈ < SIZE₄₁))
                                                          && (forall i₅₀: int ::
                                                                (  0 <= i₅₀
                                                                  && i₅₀ <= SIZE₄₁
                                                                  && (forall i₁₈: int ::
                                                                        (  0 <= i₁₈
                                                                          && i₁₈ < i₅₀
                                                                           ==> i₁₈ < SIZE₄₁))
                                                                   ==> (i₅₀ < SIZE₄₁
                                                                       ==> 0 <= i₅₀ + 1
                                                                        && i₅₀ + 1 <= SIZE₄₁
                                                                        && (forall i₁₈: int ::
                                                                              (  0 <= i₁₈
                                                                                && i₁₈ < i₅₀ + 1
                                                                                 ==> i₁₈ < SIZE₄₁)))
                                                                    &&   i₅₀ < SIZE₄₁
                                                                      ||   0 <= 0
                                                                        && 0 <= SIZE₄₁
                                                                        && (forall i₂₂: int ::
                                                                              (  0 <= i₂₂
                                                                                && i₂₂ < 0
                                                                                 ==> i₂₂ < SIZE₄₁))
                                                                        && (forall i₅₂: int ::
                                                                              (  0 <= i₅₂
                                                                                && i₅₂ <= SIZE₄₁
                                                                                && (forall i₂₂: int ::
                                                                                      (  0 <= i₂₂
                                                                                        && i₂₂ < i₅₂
                                                                                         ==> i₂₂ < SIZE₄₁))
                                                                                 ==> (i₅₂ < SIZE₄₁
                                                                                     ==> 0 <= i₅₂ + 1
                                                                                      && i₅₂ + 1 <= SIZE₄₁
                                                                                      && (forall i₂₂: int ::
                                                                                            (  0 <= i₂₂
                                                                                              && i₂₂ < i₅₂ + 1
                                                                                               ==> i₂₂ < SIZE₄₁)))
                                                                                  &&   i₅₂ < SIZE₄₁
                                                                                    ||   0 <= 0
                                                                                      && 0 <= SIZE₄₁
                                                                                      && (forall i₂₆: int ::
                                                                                            (  0 <= i₂₆
                                                                                              && i₂₆ < 0
                                                                                               ==> i₂₆ < SIZE₄₁))
                                                                                      && (forall i₅₄: int ::
                                                                                            (  0 <= i₅₄
                                                                                              && i₅₄ <= SIZE₄₁
                                                                                              && (forall i₂₆: int ::
                                                                                                    (  0 <= i₂₆
                                                                                                      && i₂₆ < i₅₄
                                                                                                       ==> i₂₆ < SIZE₄₁))
                                                                                               ==> (i₅₄ < SIZE₄₁
                                                                                                   ==> 0 <= i₅₄ + 1
                                                                                                    && i₅₄ + 1 <= SIZE₄₁
                                                                                                    && (forall i₂₆: int ::
                                                                                                          (  0 <= i₂₆
                                                                                                            && i₂₆ < i₅₄ + 1
                                                                                                             ==> i₂₆ < SIZE₄₁)))
                                                                                                &&   i₅₄ < SIZE₄₁
                                                                                                  ||   0 <= 0
                                                                                                    && 0 <= SIZE₄₁
                                                                                                    && (forall i₃₀: int ::
                                                                                                          (  0 <= i₃₀
                                                                                                            && i₃₀ < 0
                                                                                                             ==> i₃₀ < SIZE₄₁))
                                                                                                    && (forall i₅₆: int ::
                                                                                                          (  0 <= i₅₆
                                                                                                            && i₅₆ <= SIZE₄₁
                                                                                                            && (forall i₃₀: int ::
                                                                                                                  (  0 <= i₃₀
                                                                                                                    && i₃₀ < i₅₆
                                                                                                                     ==> i₃₀ < SIZE₄₁))
                                                                                                             ==> (i₅₆ < SIZE₄₁
                                                                                                                 ==> 0 <= i₅₆ + 1
                                                                                                                  && i₅₆ + 1 <= SIZE₄₁
                                                                                                                  && (forall i₃₀: int ::
                                                                                                                        (  0 <= i₃₀
                                                                                                                          && i₃₀ < i₅₆ + 1
                                                                                                                           ==> i₃₀ < SIZE₄₁)))
                                                                                                              &&   i₅₆ < SIZE₄₁
                                                                                                                ||   0 <= 0
                                                                                                                  && 0 <= SIZE₄₁
                                                                                                                  && (forall i₃₄: int ::
                                                                                                                        (  0 <= i₃₄
                                                                                                                          && i₃₄ < 0
                                                                                                                           ==> i₃₄ < SIZE₄₁))
                                                                                                                  && (forall i₅₈: int ::
                                                                                                                        (  0 <= i₅₈
                                                                                                                          && i₅₈ <= SIZE₄₁
                                                                                                                          && (forall i₃₄: int ::
                                                                                                                                (  0 <= i₃₄
                                                                                                                                  && i₃₄ < i₅₈
                                                                                                                                   ==> i₃₄ < SIZE₄₁))
                                                                                                                           ==> (i₅₈ < SIZE₄₁
                                                                                                                               ==> 0 <= i₅₈ + 1
                                                                                                                                && i₅₈ + 1 <= SIZE₄₁
                                                                                                                                && (forall i₃₄: int ::
                                                                                                                                      (  0 <= i₃₄
                                                                                                                                        && i₃₄ < i₅₈ + 1
                                                                                                                                         ==> i₃₄ < SIZE₄₁)))
                                                                                                                            &&   i₅₈ < SIZE₄₁
                                                                                                                              ||   0 <= 0
                                                                                                                                && 0 <= SIZE₄₁
                                                                                                                                && (forall i₃₈: int ::
                                                                                                                                      (  0 <= i₃₈
                                                                                                                                        && i₃₈ < 0
                                                                                                                                         ==> i₃₈ < SIZE₄₁))
                                                                                                                                && (forall sum₅₉: int, i₆₀: int ::
                                                                                                                                      (  0 <= i₆₀
                                                                                                                                        && i₆₀ <= SIZE₄₁
                                                                                                                                        && (forall i₃₈: int ::
                                                                                                                                              (  0 <= i₃₈
                                                                                                                                                && i₃₈ < i₆₀
                                                                                                                                                 ==> i₃₈ < SIZE₄₁))
                                                                                                                                         ==> (i₆₀ < SIZE₄₁
                                                                                                                                             ==> 0 <= i₆₀ + 1
                                                                                                                                              && i₆₀ + 1 <= SIZE₄₁
                                                                                                                                              && (forall i₃₈: int ::
                                                                                                                                                    (  0 <= i₃₈
                                                                                                                                                      && i₃₈ < i₆₀ + 1
                                                                                                                                                       ==> i₃₈ < SIZE₄₁)))
                                                                                                                                          &&   i₆₀ < SIZE₄₁
                                                                                                                                            || sum₅₉ == 0)))))))))))))))))))));


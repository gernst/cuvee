data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall src: [int]int, dst: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < 0
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 100000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < 0
                        && src[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < 0)
                || src[x₅] == src[x₅])
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < 0
                 ==> i₄ < 100000))
        && (forall src₁₅: [int]int, i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ <= 100000
                && (forall x₅: int, i₄: int ::
                      (  x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₆
                         ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                i₄ < 100000
                                && x₅ == i₄
                                && 0 <= i₄
                                && i₄ < i₁₆
                                && src₁₅[x₅] == __VERIFIER_nondet_int₁₃)))
                && (forall x₅: int ::
                        (exists i₄: int ::
                                x₅ == i₄
                                && 0 <= i₄
                                && i₄ < i₁₆)
                        || src₁₅[x₅] == src[x₅])
                && (forall i₄: int ::
                      (  0 <= i₄
                        && i₄ < i₁₆
                         ==> i₄ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (i₁₆ < 100000
                           ==> 0 <= i₁₆ + 1
                            && i₁₆ + 1 <= 100000
                            && (forall x₅: int, i₄: int ::
                                  (  x₅ == i₄
                                    && 0 <= i₄
                                    && i₄ < i₁₆ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                            i₄ < 100000
                                            && x₅ == i₄
                                            && 0 <= i₄
                                            && i₄ < i₁₆ + 1
                                            && src₁₅[i₁₆ := __VERIFIER_nondet_int₁][x₅] == __VERIFIER_nondet_int₁₃)))
                            && (forall x₅: int ::
                                    (exists i₄: int ::
                                            x₅ == i₄
                                            && 0 <= i₄
                                            && i₄ < i₁₆ + 1)
                                    || src₁₅[i₁₆ := __VERIFIER_nondet_int₁][x₅] == src[x₅])
                            && (forall i₄: int ::
                                  (  0 <= i₄
                                    && i₄ < i₁₆ + 1
                                     ==> i₄ < 100000))))
                  &&   i₁₆ < 100000
                    ||   0 <= 0
                      && (forall x₉: int, i₈: int ::
                            (  x₉ == i₈
                              && 0 <= i₈
                              && i₈ < 0
                               ==> (exists i₈: int ::
                                    (src₁₅[i₈] == 0
                                       ==> false))))
                      && (forall x₉: int ::
                              (exists i₈: int ::
                                      x₉ == i₈
                                      && 0 <= i₈
                                      && i₈ < 0)
                              || dst[x₉] == dst[x₉])
                      && (forall i₈: int ::
                            (  0 <= i₈
                              && i₈ < 0
                              && src₁₅[i₈] == 0
                               ==> false))
                      && (forall dst₁₇: [int]int, i₁₈: int ::
                            (  0 <= i₁₈
                              && (forall x₉: int, i₈: int ::
                                    (  x₉ == i₈
                                      && 0 <= i₈
                                      && i₈ < i₁₈
                                       ==> (exists i₈: int ::
                                            (src₁₅[i₈] == 0
                                               ==> false))))
                              && (forall x₉: int ::
                                      (exists i₈: int ::
                                              x₉ == i₈
                                              && 0 <= i₈
                                              && i₈ < i₁₈)
                                      || dst₁₇[x₉] == dst[x₉])
                              && (forall i₈: int ::
                                    (  0 <= i₈
                                      && i₈ < i₁₈
                                      && src₁₅[i₈] == 0
                                       ==> false))
                               ==> src₁₅[i₁₈] == 0
                                  ||   0 <= i₁₈ + 1
                                    && (forall x₉: int, i₈: int ::
                                          (  x₉ == i₈
                                            && 0 <= i₈
                                            && i₈ < i₁₈ + 1
                                             ==> (exists i₈: int ::
                                                  (src₁₅[i₈] == 0
                                                     ==> false))))
                                    && (forall x₉: int ::
                                            (exists i₈: int ::
                                                    x₉ == i₈
                                                    && 0 <= i₈
                                                    && i₈ < i₁₈ + 1)
                                            || dst₁₇[i₁₈ := src₁₅[i₁₈]][x₉] == dst[x₉])
                                    && (forall i₈: int ::
                                          (  0 <= i₈
                                            && i₈ < i₁₈ + 1
                                            && src₁₅[i₈] == 0
                                             ==> false))
                                && (src₁₅[i₁₈] == 0
                                   ==> 0 <= 0
                                    && 0 <= i₁₈
                                    && (forall x₁₃: int ::
                                          (  0 <= x₁₃
                                            && x₁₃ < 0
                                             ==> x₁₃ < i₁₈))
                                    && (forall x₁₉: int ::
                                          (  0 <= x₁₉
                                            && x₁₉ <= i₁₈
                                            && (forall x₁₃: int ::
                                                  (  0 <= x₁₃
                                                    && x₁₃ < x₁₉
                                                     ==> x₁₃ < i₁₈))
                                             ==> (x₁₉ < i₁₈
                                               ==> dst₁₇[x₁₉] == src₁₅[x₁₉]
                                                && 0 <= x₁₉ + 1
                                                && x₁₉ + 1 <= i₁₈
                                                && (forall x₁₃: int ::
                                                      (  0 <= x₁₃
                                                        && x₁₃ < x₁₉ + 1
                                                         ==> x₁₃ < i₁₈)))))))))));


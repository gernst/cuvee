data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall src: [int]int, dst: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₅: int, j₄: int ::
              (  x₅ == j₄
                && 0 <= j₄
                && j₄ < 0
                 ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                        j₄ < 100000
                        && x₅ == j₄
                        && 0 <= j₄
                        && j₄ < 0
                        && src[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists j₄: int ::
                        x₅ == j₄
                        && 0 <= j₄
                        && j₄ < 0)
                || src[x₅] == src[x₅])
        && (forall j₄: int ::
              (  0 <= j₄
                && j₄ < 0
                 ==> j₄ < 100000))
        && (forall src₁₄: [int]int, j₁₅: int ::
              (  0 <= j₁₅
                && j₁₅ <= 100000
                && (forall x₅: int, j₄: int ::
                      (  x₅ == j₄
                        && 0 <= j₄
                        && j₄ < j₁₅
                         ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                                j₄ < 100000
                                && x₅ == j₄
                                && 0 <= j₄
                                && j₄ < j₁₅
                                && src₁₄[x₅] == __VERIFIER_nondet_int₁₃)))
                && (forall x₅: int ::
                        (exists j₄: int ::
                                x₅ == j₄
                                && 0 <= j₄
                                && j₄ < j₁₅)
                        || src₁₄[x₅] == src[x₅])
                && (forall j₄: int ::
                      (  0 <= j₄
                        && j₄ < j₁₅
                         ==> j₄ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (j₁₅ < 100000
                           ==> 0 <= j₁₅ + 1
                            && j₁₅ + 1 <= 100000
                            && (forall x₅: int, j₄: int ::
                                  (  x₅ == j₄
                                    && 0 <= j₄
                                    && j₄ < j₁₅ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₃: int, j₄: int ::
                                            j₄ < 100000
                                            && x₅ == j₄
                                            && 0 <= j₄
                                            && j₄ < j₁₅ + 1
                                            && src₁₄[j₁₅ := __VERIFIER_nondet_int₁][x₅] == __VERIFIER_nondet_int₁₃)))
                            && (forall x₅: int ::
                                    (exists j₄: int ::
                                            x₅ == j₄
                                            && 0 <= j₄
                                            && j₄ < j₁₅ + 1)
                                    || src₁₄[j₁₅ := __VERIFIER_nondet_int₁][x₅] == src[x₅])
                            && (forall j₄: int ::
                                  (  0 <= j₄
                                    && j₄ < j₁₅ + 1
                                     ==> j₄ < 100000))))
                  &&   j₁₅ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₉: int, i₈: int ::
                            (  x₉ == i₈
                              && 0 <= i₈
                              && i₈ < 0
                               ==> (exists i₈: int ::
                                      i₈ < 100000
                                      && (src₁₄[i₈] == 0
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
                               ==> i₈ < 100000
                                && (src₁₄[i₈] == 0
                                   ==> false)))
                      && (forall dst₁₆: [int]int, i₁₇: int ::
                            (  0 <= i₁₇
                              && i₁₇ <= 100000
                              && (forall x₉: int, i₈: int ::
                                    (  x₉ == i₈
                                      && 0 <= i₈
                                      && i₈ < i₁₇
                                       ==> (exists i₈: int ::
                                              i₈ < 100000
                                              && (src₁₄[i₈] == 0
                                                 ==> false))))
                              && (forall x₉: int ::
                                      (exists i₈: int ::
                                              x₉ == i₈
                                              && 0 <= i₈
                                              && i₈ < i₁₇)
                                      || dst₁₆[x₉] == dst[x₉])
                              && (forall i₈: int ::
                                    (  0 <= i₈
                                      && i₈ < i₁₇
                                       ==> i₈ < 100000
                                        && (src₁₄[i₈] == 0
                                           ==> false)))
                               ==> (i₁₇ < 100000
                                   ==> src₁₄[i₁₇] == 0
                                    ||   0 <= i₁₇ + 1
                                      && i₁₇ + 1 <= 100000
                                      && (forall x₉: int, i₈: int ::
                                            (  x₉ == i₈
                                              && 0 <= i₈
                                              && i₈ < i₁₇ + 1
                                               ==> (exists i₈: int ::
                                                      i₈ < 100000
                                                      && (src₁₄[i₈] == 0
                                                         ==> false))))
                                      && (forall x₉: int ::
                                              (exists i₈: int ::
                                                      x₉ == i₈
                                                      && 0 <= i₈
                                                      && i₈ < i₁₇ + 1)
                                              || dst₁₆[i₁₇ := src₁₄[i₁₇]][x₉] == dst[x₉])
                                      && (forall i₈: int ::
                                            (  0 <= i₈
                                              && i₈ < i₁₇ + 1
                                               ==> i₈ < 100000
                                                && (src₁₄[i₈] == 0
                                                   ==> false))))
                                &&     i₁₇ < 100000
                                    && (src₁₄[i₁₇] == 0
                                       ==> false)
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall i₁₂: int ::
                                          (  0 <= i₁₂
                                            && i₁₂ < 0
                                             ==> i₁₂ < 100000
                                              && (src₁₄[i₁₂] == 0
                                                 ==> false)))
                                    && (forall i₁₈: int ::
                                          (  0 <= i₁₈
                                            && i₁₈ <= 100000
                                            && (forall i₁₂: int ::
                                                  (  0 <= i₁₂
                                                    && i₁₂ < i₁₈
                                                     ==> i₁₂ < 100000
                                                      && (src₁₄[i₁₂] == 0
                                                         ==> false)))
                                             ==> (i₁₈ < 100000
                                               ==> src₁₄[i₁₈] == 0
                                                ||   dst₁₆[i₁₈] == src₁₄[i₁₈]
                                                  && 0 <= i₁₈ + 1
                                                  && i₁₈ + 1 <= 100000
                                                  && (forall i₁₂: int ::
                                                        (  0 <= i₁₂
                                                          && i₁₂ < i₁₈ + 1
                                                           ==> i₁₂ < 100000
                                                            && (src₁₄[i₁₂] == 0
                                                               ==> false)))))))))));


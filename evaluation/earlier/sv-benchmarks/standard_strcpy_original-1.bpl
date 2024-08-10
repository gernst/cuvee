data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

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
        && (forall src₁₄: [int]int, i₁₅: int ::
              (  0 <= i₁₅
                && i₁₅ <= 100000
                && (forall x₅: int, i₄: int ::
                      (  x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₅
                         ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                i₄ < 100000
                                && x₅ == i₄
                                && 0 <= i₄
                                && i₄ < i₁₅
                                && src₁₄[x₅] == __VERIFIER_nondet_int₁₃)))
                && (forall x₅: int ::
                        (exists i₄: int ::
                                x₅ == i₄
                                && 0 <= i₄
                                && i₄ < i₁₅)
                        || src₁₄[x₅] == src[x₅])
                && (forall i₄: int ::
                      (  0 <= i₄
                        && i₄ < i₁₅
                         ==> i₄ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (i₁₅ < 100000
                           ==> 0 <= i₁₅ + 1
                            && i₁₅ + 1 <= 100000
                            && (forall x₅: int, i₄: int ::
                                  (  x₅ == i₄
                                    && 0 <= i₄
                                    && i₄ < i₁₅ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                            i₄ < 100000
                                            && x₅ == i₄
                                            && 0 <= i₄
                                            && i₄ < i₁₅ + 1
                                            && src₁₄[i₁₅ := __VERIFIER_nondet_int₁][x₅] == __VERIFIER_nondet_int₁₃)))
                            && (forall x₅: int ::
                                    (exists i₄: int ::
                                            x₅ == i₄
                                            && 0 <= i₄
                                            && i₄ < i₁₅ + 1)
                                    || src₁₄[i₁₅ := __VERIFIER_nondet_int₁][x₅] == src[x₅])
                            && (forall i₄: int ::
                                  (  0 <= i₄
                                    && i₄ < i₁₅ + 1
                                     ==> i₄ < 100000))))
                  &&   i₁₅ < 100000
                    ||   0 <= 0
                      && (forall x₉: int, i₈: int ::
                            (  x₉ == i₈
                              && 0 <= i₈
                              && i₈ < 0
                               ==> (exists i₈: int ::
                                    (src₁₄[i₈] == 0
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
                              && src₁₄[i₈] == 0
                               ==> false))
                      && (forall dst₁₆: [int]int, i₁₇: int ::
                            (  0 <= i₁₇
                              && (forall x₉: int, i₈: int ::
                                    (  x₉ == i₈
                                      && 0 <= i₈
                                      && i₈ < i₁₇
                                       ==> (exists i₈: int ::
                                            (src₁₄[i₈] == 0
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
                                      && src₁₄[i₈] == 0
                                       ==> false))
                               ==> src₁₄[i₁₇] == 0
                                  ||   0 <= i₁₇ + 1
                                    && (forall x₉: int, i₈: int ::
                                          (  x₉ == i₈
                                            && 0 <= i₈
                                            && i₈ < i₁₇ + 1
                                             ==> (exists i₈: int ::
                                                  (src₁₄[i₈] == 0
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
                                            && src₁₄[i₈] == 0
                                             ==> false))
                                && (src₁₄[i₁₇] == 0
                                   ==> 0 <= 0
                                    && (forall i₁₂: int ::
                                          (  0 <= i₁₂
                                            && i₁₂ < 0
                                            && src₁₄[i₁₂] == 0
                                             ==> false))
                                    && (forall i₁₈: int ::
                                          (  0 <= i₁₈
                                            && (forall i₁₂: int ::
                                                  (  0 <= i₁₂
                                                    && i₁₂ < i₁₈
                                                    && src₁₄[i₁₂] == 0
                                                     ==> false))
                                             ==> src₁₄[i₁₈] == 0
                                              ||   dst₁₆[i₁₈] == src₁₄[i₁₈]
                                                && 0 <= i₁₈ + 1
                                                && (forall i₁₂: int ::
                                                      (  0 <= i₁₂
                                                        && i₁₂ < i₁₈ + 1
                                                        && src₁₄[i₁₂] == 0
                                                         ==> false))))))))));


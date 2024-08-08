data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₇: int, a₆: int ::
              (  x₇ == a₆
                && 0 <= a₆
                && a₆ < 0
                 ==> (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                        a₆ < 100000
                        && x₇ == a₆
                        && 0 <= a₆
                        && a₆ < 0
                        && a1[x₇] == __VERIFIER_nondet_int₁₄)))
        && (forall x₇: int ::
                (exists a₆: int ::
                        x₇ == a₆
                        && 0 <= a₆
                        && a₆ < 0)
                || a1[x₇] == a1[x₇])
        && (forall x₈: int, a₆: int ::
              (  x₈ == a₆
                && 0 <= a₆
                && a₆ < 0
                 ==> (exists __VERIFIER_nondet_int₂₅: int, a₆: int ::
                        a₆ < 100000
                        && x₈ == a₆
                        && 0 <= a₆
                        && a₆ < 0
                        && a2[x₈] == __VERIFIER_nondet_int₂₅)))
        && (forall x₈: int ::
                (exists a₆: int ::
                        x₈ == a₆
                        && 0 <= a₆
                        && a₆ < 0)
                || a2[x₈] == a2[x₈])
        && (forall a₆: int ::
              (  0 <= a₆
                && a₆ < 0
                 ==> a₆ < 100000))
        && (forall a1₂₀: [int]int, a2₂₁: [int]int, a₂₂: int ::
              (  0 <= a₂₂
                && a₂₂ <= 100000
                && (forall x₇: int, a₆: int ::
                      (  x₇ == a₆
                        && 0 <= a₆
                        && a₆ < a₂₂
                         ==> (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                                a₆ < 100000
                                && x₇ == a₆
                                && 0 <= a₆
                                && a₆ < a₂₂
                                && a1₂₀[x₇] == __VERIFIER_nondet_int₁₄)))
                && (forall x₇: int ::
                        (exists a₆: int ::
                                x₇ == a₆
                                && 0 <= a₆
                                && a₆ < a₂₂)
                        || a1₂₀[x₇] == a1[x₇])
                && (forall x₈: int, a₆: int ::
                      (  x₈ == a₆
                        && 0 <= a₆
                        && a₆ < a₂₂
                         ==> (exists __VERIFIER_nondet_int₂₅: int, a₆: int ::
                                a₆ < 100000
                                && x₈ == a₆
                                && 0 <= a₆
                                && a₆ < a₂₂
                                && a2₂₁[x₈] == __VERIFIER_nondet_int₂₅)))
                && (forall x₈: int ::
                        (exists a₆: int ::
                                x₈ == a₆
                                && 0 <= a₆
                                && a₆ < a₂₂)
                        || a2₂₁[x₈] == a2[x₈])
                && (forall a₆: int ::
                      (  0 <= a₆
                        && a₆ < a₂₂
                         ==> a₆ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (a₂₂ < 100000
                           ==> 0 <= a₂₂ + 1
                            && a₂₂ + 1 <= 100000
                            && (forall x₇: int, a₆: int ::
                                  (  x₇ == a₆
                                    && 0 <= a₆
                                    && a₆ < a₂₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₄: int, a₆: int ::
                                            a₆ < 100000
                                            && x₇ == a₆
                                            && 0 <= a₆
                                            && a₆ < a₂₂ + 1
                                            && a1₂₀[a₂₂ := __VERIFIER_nondet_int₁][x₇] == __VERIFIER_nondet_int₁₄)))
                            && (forall x₇: int ::
                                    (exists a₆: int ::
                                            x₇ == a₆
                                            && 0 <= a₆
                                            && a₆ < a₂₂ + 1)
                                    || a1₂₀[a₂₂ := __VERIFIER_nondet_int₁][x₇] == a1[x₇])
                            && (forall x₈: int, a₆: int ::
                                  (  x₈ == a₆
                                    && 0 <= a₆
                                    && a₆ < a₂₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₅: int, a₆: int ::
                                            a₆ < 100000
                                            && x₈ == a₆
                                            && 0 <= a₆
                                            && a₆ < a₂₂ + 1
                                            && a2₂₁[a₂₂ := __VERIFIER_nondet_int₂][x₈] == __VERIFIER_nondet_int₂₅)))
                            && (forall x₈: int ::
                                    (exists a₆: int ::
                                            x₈ == a₆
                                            && 0 <= a₆
                                            && a₆ < a₂₂ + 1)
                                    || a2₂₁[a₂₂ := __VERIFIER_nondet_int₂][x₈] == a2[x₈])
                            && (forall a₆: int ::
                                  (  0 <= a₆
                                    && a₆ < a₂₂ + 1
                                     ==> a₆ < 100000))))
                  &&   a₂₂ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₁₄: int, i₁₃: int ::
                            (  x₁₄ == i₁₃
                              && 0 <= i₁₃
                              && i₁₃ < 0
                               ==> (exists i₁₃: int ::
                                      i₁₃ < 100000
                                      && x₁₄ == i₁₃
                                      && 0 <= i₁₃
                                      && i₁₃ < 0
                                      && a1₂₀[x₁₄] == a1₂₀[i₁₃])))
                      && (forall x₁₄: int ::
                              (exists i₁₃: int ::
                                      x₁₄ == i₁₃
                                      && 0 <= i₁₃
                                      && i₁₃ < 0)
                              || a1₂₀[x₁₄] == a1₂₀[x₁₄])
                      && (forall i₁₃: int ::
                            (  0 <= i₁₃
                              && i₁₃ < 0
                               ==> i₁₃ < 100000))
                      && (forall a1₂₃: [int]int, i₂₄: int ::
                            (  0 <= i₂₄
                              && i₂₄ <= 100000
                              && (forall x₁₄: int, i₁₃: int ::
                                    (  x₁₄ == i₁₃
                                      && 0 <= i₁₃
                                      && i₁₃ < i₂₄
                                       ==> (exists i₁₃: int ::
                                              i₁₃ < 100000
                                              && x₁₄ == i₁₃
                                              && 0 <= i₁₃
                                              && i₁₃ < i₂₄
                                              && a1₂₃[x₁₄] == a1₂₀[i₁₃])))
                              && (forall x₁₄: int ::
                                      (exists i₁₃: int ::
                                              x₁₄ == i₁₃
                                              && 0 <= i₁₃
                                              && i₁₃ < i₂₄)
                                      || a1₂₃[x₁₄] == a1₂₀[x₁₄])
                              && (forall i₁₃: int ::
                                    (  0 <= i₁₃
                                      && i₁₃ < i₂₄
                                       ==> i₁₃ < 100000))
                               ==> (i₂₄ < 100000
                                   ==> 0 <= i₂₄ + 1
                                    && i₂₄ + 1 <= 100000
                                    && (forall x₁₄: int, i₁₃: int ::
                                          (  x₁₄ == i₁₃
                                            && 0 <= i₁₃
                                            && i₁₃ < i₂₄ + 1
                                             ==> (exists i₁₃: int ::
                                                    i₁₃ < 100000
                                                    && x₁₄ == i₁₃
                                                    && 0 <= i₁₃
                                                    && i₁₃ < i₂₄ + 1
                                                    && a1₂₃[i₂₄ := a1₂₃[i₂₄]][x₁₄] == a1₂₀[i₁₃])))
                                    && (forall x₁₄: int ::
                                            (exists i₁₃: int ::
                                                    x₁₄ == i₁₃
                                                    && 0 <= i₁₃
                                                    && i₁₃ < i₂₄ + 1)
                                            || a1₂₃[i₂₄ := a1₂₃[i₂₄]][x₁₄] == a1₂₀[x₁₄])
                                    && (forall i₁₃: int ::
                                          (  0 <= i₁₃
                                            && i₁₃ < i₂₄ + 1
                                             ==> i₁₃ < 100000)))
                                &&   i₂₄ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₁₈: int ::
                                          (  0 <= x₁₈
                                            && x₁₈ < 0
                                             ==> x₁₈ < 100000))
                                    && (forall x₂₅: int ::
                                          (  0 <= x₂₅
                                            && x₂₅ <= 100000
                                            && (forall x₁₈: int ::
                                                  (  0 <= x₁₈
                                                    && x₁₈ < x₂₅
                                                     ==> x₁₈ < 100000))
                                             ==> (x₂₅ < 100000
                                               ==> a1₂₃[x₂₅] == a2₂₁[x₂₅]
                                                && 0 <= x₂₅ + 1
                                                && x₂₅ + 1 <= 100000
                                                && (forall x₁₈: int ::
                                                      (  0 <= x₁₈
                                                        && x₁₈ < x₂₅ + 1
                                                         ==> x₁₈ < 100000))))))))));


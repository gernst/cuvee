data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int ::
        0 <= 0
        && 0 <= 200000
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < 0
                 ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                        i₇ < 200000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < 0
                        && a1[x₈] == __VERIFIER_nondet_int₁₅)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < 0)
                || a1[x₈] == a1[x₈])
        && (forall x₉: int, i₇: int ::
              (  x₉ == i₇
                && 0 <= i₇
                && i₇ < 0
                 ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                        i₇ < 200000
                        && x₉ == i₇
                        && 0 <= i₇
                        && i₇ < 0
                        && a2[x₉] == __VERIFIER_nondet_int₂₆)))
        && (forall x₉: int ::
                (exists i₇: int ::
                        x₉ == i₇
                        && 0 <= i₇
                        && i₇ < 0)
                || a2[x₉] == a2[x₉])
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < 0
                 ==> i₇ < 200000))
        && (forall a1₂₀: [int]int, a2₂₁: [int]int, i₂₂: int ::
              (  0 <= i₂₂
                && i₂₂ <= 200000
                && (forall x₈: int, i₇: int ::
                      (  x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₂
                         ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                i₇ < 200000
                                && x₈ == i₇
                                && 0 <= i₇
                                && i₇ < i₂₂
                                && a1₂₀[x₈] == __VERIFIER_nondet_int₁₅)))
                && (forall x₈: int ::
                        (exists i₇: int ::
                                x₈ == i₇
                                && 0 <= i₇
                                && i₇ < i₂₂)
                        || a1₂₀[x₈] == a1[x₈])
                && (forall x₉: int, i₇: int ::
                      (  x₉ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₂
                         ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                                i₇ < 200000
                                && x₉ == i₇
                                && 0 <= i₇
                                && i₇ < i₂₂
                                && a2₂₁[x₉] == __VERIFIER_nondet_int₂₆)))
                && (forall x₉: int ::
                        (exists i₇: int ::
                                x₉ == i₇
                                && 0 <= i₇
                                && i₇ < i₂₂)
                        || a2₂₁[x₉] == a2[x₉])
                && (forall i₇: int ::
                      (  0 <= i₇
                        && i₇ < i₂₂
                         ==> i₇ < 200000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (i₂₂ < 200000
                           ==> 0 <= i₂₂ + 1
                            && i₂₂ + 1 <= 200000
                            && (forall x₈: int, i₇: int ::
                                  (  x₈ == i₇
                                    && 0 <= i₇
                                    && i₇ < i₂₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₅: int, i₇: int ::
                                            i₇ < 200000
                                            && x₈ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₂₂ + 1
                                            && a1₂₀[i₂₂ := __VERIFIER_nondet_int₁][x₈] == __VERIFIER_nondet_int₁₅)))
                            && (forall x₈: int ::
                                    (exists i₇: int ::
                                            x₈ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₂₂ + 1)
                                    || a1₂₀[i₂₂ := __VERIFIER_nondet_int₁][x₈] == a1[x₈])
                            && (forall x₉: int, i₇: int ::
                                  (  x₉ == i₇
                                    && 0 <= i₇
                                    && i₇ < i₂₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₆: int, i₇: int ::
                                            i₇ < 200000
                                            && x₉ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₂₂ + 1
                                            && a2₂₁[i₂₂ := __VERIFIER_nondet_int₂][x₉] == __VERIFIER_nondet_int₂₆)))
                            && (forall x₉: int ::
                                    (exists i₇: int ::
                                            x₉ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₂₂ + 1)
                                    || a2₂₁[i₂₂ := __VERIFIER_nondet_int₂][x₉] == a2[x₉])
                            && (forall i₇: int ::
                                  (  0 <= i₇
                                    && i₇ < i₂₂ + 1
                                     ==> i₇ < 200000))))
                  &&   i₂₂ < 200000
                    ||   0 <= 0
                      && 0 <= 200000
                      && (forall x₁₄: int, i₁₃: int ::
                            (  x₁₄ == i₁₃
                              && 0 <= i₁₃
                              && i₁₃ < 0
                               ==> (exists i₁₃: int ::
                                    (i₁₃ == 150000
                                       ==> false))))
                      && (forall x₁₄: int ::
                              (exists i₁₃: int ::
                                      x₁₄ == i₁₃
                                      && 0 <= i₁₃
                                      && i₁₃ < 0)
                              || a2₂₁[x₁₄] == a2₂₁[x₁₄])
                      && (forall i₁₃: int ::
                            (  0 <= i₁₃
                              && i₁₃ < 0
                               ==> i₁₃ < 200000))
                      && (forall a2₂₃: [int]int, i₂₄: int ::
                            (  0 <= i₂₄
                              && i₂₄ <= 200000
                              && (forall x₁₄: int, i₁₃: int ::
                                    (  x₁₄ == i₁₃
                                      && 0 <= i₁₃
                                      && i₁₃ < i₂₄
                                       ==> (exists i₁₃: int ::
                                            (i₁₃ == 150000
                                               ==> false))))
                              && (forall x₁₄: int ::
                                      (exists i₁₃: int ::
                                              x₁₄ == i₁₃
                                              && 0 <= i₁₃
                                              && i₁₃ < i₂₄)
                                      || a2₂₃[x₁₄] == a2₂₁[x₁₄])
                              && (forall i₁₃: int ::
                                    (  0 <= i₁₃
                                      && i₁₃ < i₂₄
                                       ==> i₁₃ < 200000))
                               ==> (i₂₄ < 200000
                                   ==> i₂₄ == 150000
                                      ||   0 <= i₂₄ + 1
                                        && i₂₄ + 1 <= 200000
                                        && (forall x₁₄: int, i₁₃: int ::
                                              (  x₁₄ == i₁₃
                                                && 0 <= i₁₃
                                                && i₁₃ < i₂₄ + 1
                                                 ==> (exists i₁₃: int ::
                                                      (i₁₃ == 150000
                                                         ==> false))))
                                        && (forall x₁₄: int ::
                                                (exists i₁₃: int ::
                                                        x₁₄ == i₁₃
                                                        && 0 <= i₁₃
                                                        && i₁₃ < i₂₄ + 1)
                                                || a2₂₃[i₂₄ := a1₂₀[i₂₄]][x₁₄] == a2₂₁[x₁₄])
                                        && (forall i₁₃: int ::
                                              (  0 <= i₁₃
                                                && i₁₃ < i₂₄ + 1
                                                 ==> i₁₃ < 200000))
                                    && (i₂₄ == 150000
                                       ==> 0 <= i₂₄ + 1
                                        && i₂₄ + 1 <= 200000
                                        && (forall x₁₄: int, i₁₃: int ::
                                              (  x₁₄ == i₁₃
                                                && 0 <= i₁₃
                                                && i₁₃ < i₂₄ + 1
                                                 ==> (exists i₁₃: int ::
                                                      (i₁₃ == 150000
                                                         ==> false))))
                                        && (forall x₁₄: int ::
                                                (exists i₁₃: int ::
                                                        x₁₄ == i₁₃
                                                        && 0 <= i₁₃
                                                        && i₁₃ < i₂₄ + 1)
                                                || a2₂₃[x₁₄] == a2₂₁[x₁₄])
                                        && (forall i₁₃: int ::
                                              (  0 <= i₁₃
                                                && i₁₃ < i₂₄ + 1
                                                 ==> i₁₃ < 200000))))
                                &&   i₂₄ < 200000
                                  ||   0 <= 0
                                    && 0 <= 200000
                                    && (forall x₁₈: int ::
                                          (  0 <= x₁₈
                                            && x₁₈ < 0
                                             ==> x₁₈ < 200000))
                                    && (forall x₂₅: int ::
                                          (  0 <= x₂₅
                                            && x₂₅ <= 200000
                                            && (forall x₁₈: int ::
                                                  (  0 <= x₁₈
                                                    && x₁₈ < x₂₅
                                                     ==> x₁₈ < 200000))
                                             ==> (x₂₅ < 200000
                                               ==> x₂₅ == 150000
                                                  ||   a1₂₀[x₂₅] == a2₂₃[x₂₅]
                                                    && 0 <= x₂₅ + 1
                                                    && x₂₅ + 1 <= 200000
                                                    && (forall x₁₈: int ::
                                                          (  0 <= x₁₈
                                                            && x₁₈ < x₂₅ + 1
                                                             ==> x₁₈ < 200000))
                                                && (x₂₅ == 150000
                                                   ==> 0 <= x₂₅ + 1
                                                    && x₂₅ + 1 <= 200000
                                                    && (forall x₁₈: int ::
                                                          (  0 <= x₁₈
                                                            && x₁₈ < x₂₅ + 1
                                                             ==> x₁₈ < 200000)))))))))));


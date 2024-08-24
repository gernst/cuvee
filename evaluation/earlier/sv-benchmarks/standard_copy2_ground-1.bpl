data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int, a3: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₈: int, a₇: int ::
              (  x₈ == a₇
                && 0 <= a₇
                && a₇ < 0
                 ==> (exists __VERIFIER_nondet_int₁₅: int, a₇: int ::
                        a₇ < 100000
                        && x₈ == a₇
                        && 0 <= a₇
                        && a₇ < 0
                        && a1[x₈] == __VERIFIER_nondet_int₁₅)))
        && (forall x₈: int ::
                (exists a₇: int ::
                        x₈ == a₇
                        && 0 <= a₇
                        && a₇ < 0)
                || a1[x₈] == a1[x₈])
        && (forall x₉: int, a₇: int ::
              (  x₉ == a₇
                && 0 <= a₇
                && a₇ < 0
                 ==> (exists __VERIFIER_nondet_int₂₆: int, a₇: int ::
                        a₇ < 100000
                        && x₉ == a₇
                        && 0 <= a₇
                        && a₇ < 0
                        && a2[x₉] == __VERIFIER_nondet_int₂₆)))
        && (forall x₉: int ::
                (exists a₇: int ::
                        x₉ == a₇
                        && 0 <= a₇
                        && a₇ < 0)
                || a2[x₉] == a2[x₉])
        && (forall a₇: int ::
              (  0 <= a₇
                && a₇ < 0
                 ==> a₇ < 100000))
        && (forall a1₂₅: [int]int, a2₂₆: [int]int, a₂₇: int ::
              (  0 <= a₂₇
                && a₂₇ <= 100000
                && (forall x₈: int, a₇: int ::
                      (  x₈ == a₇
                        && 0 <= a₇
                        && a₇ < a₂₇
                         ==> (exists __VERIFIER_nondet_int₁₅: int, a₇: int ::
                                a₇ < 100000
                                && x₈ == a₇
                                && 0 <= a₇
                                && a₇ < a₂₇
                                && a1₂₅[x₈] == __VERIFIER_nondet_int₁₅)))
                && (forall x₈: int ::
                        (exists a₇: int ::
                                x₈ == a₇
                                && 0 <= a₇
                                && a₇ < a₂₇)
                        || a1₂₅[x₈] == a1[x₈])
                && (forall x₉: int, a₇: int ::
                      (  x₉ == a₇
                        && 0 <= a₇
                        && a₇ < a₂₇
                         ==> (exists __VERIFIER_nondet_int₂₆: int, a₇: int ::
                                a₇ < 100000
                                && x₉ == a₇
                                && 0 <= a₇
                                && a₇ < a₂₇
                                && a2₂₆[x₉] == __VERIFIER_nondet_int₂₆)))
                && (forall x₉: int ::
                        (exists a₇: int ::
                                x₉ == a₇
                                && 0 <= a₇
                                && a₇ < a₂₇)
                        || a2₂₆[x₉] == a2[x₉])
                && (forall a₇: int ::
                      (  0 <= a₇
                        && a₇ < a₂₇
                         ==> a₇ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (a₂₇ < 100000
                           ==> 0 <= a₂₇ + 1
                            && a₂₇ + 1 <= 100000
                            && (forall x₈: int, a₇: int ::
                                  (  x₈ == a₇
                                    && 0 <= a₇
                                    && a₇ < a₂₇ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₅: int, a₇: int ::
                                            a₇ < 100000
                                            && x₈ == a₇
                                            && 0 <= a₇
                                            && a₇ < a₂₇ + 1
                                            && a1₂₅[a₂₇ := __VERIFIER_nondet_int₁][x₈] == __VERIFIER_nondet_int₁₅)))
                            && (forall x₈: int ::
                                    (exists a₇: int ::
                                            x₈ == a₇
                                            && 0 <= a₇
                                            && a₇ < a₂₇ + 1)
                                    || a1₂₅[a₂₇ := __VERIFIER_nondet_int₁][x₈] == a1[x₈])
                            && (forall x₉: int, a₇: int ::
                                  (  x₉ == a₇
                                    && 0 <= a₇
                                    && a₇ < a₂₇ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₆: int, a₇: int ::
                                            a₇ < 100000
                                            && x₉ == a₇
                                            && 0 <= a₇
                                            && a₇ < a₂₇ + 1
                                            && a2₂₆[a₂₇ := __VERIFIER_nondet_int₂][x₉] == __VERIFIER_nondet_int₂₆)))
                            && (forall x₉: int ::
                                    (exists a₇: int ::
                                            x₉ == a₇
                                            && 0 <= a₇
                                            && a₇ < a₂₇ + 1)
                                    || a2₂₆[a₂₇ := __VERIFIER_nondet_int₂][x₉] == a2[x₉])
                            && (forall a₇: int ::
                                  (  0 <= a₇
                                    && a₇ < a₂₇ + 1
                                     ==> a₇ < 100000))))
                  &&   a₂₇ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₁₅: int, i₁₄: int ::
                            (  x₁₅ == i₁₄
                              && 0 <= i₁₄
                              && i₁₄ < 0
                               ==> (exists i₁₄: int ::
                                      i₁₄ < 100000
                                      && x₁₅ == i₁₄
                                      && 0 <= i₁₄
                                      && i₁₄ < 0
                                      && a3[x₁₅] == a1₂₅[i₁₄])))
                      && (forall x₁₅: int ::
                              (exists i₁₄: int ::
                                      x₁₅ == i₁₄
                                      && 0 <= i₁₄
                                      && i₁₄ < 0)
                              || a3[x₁₅] == a3[x₁₅])
                      && (forall i₁₄: int ::
                            (  0 <= i₁₄
                              && i₁₄ < 0
                               ==> i₁₄ < 100000))
                      && (forall a3₂₈: [int]int, i₂₉: int ::
                            (  0 <= i₂₉
                              && i₂₉ <= 100000
                              && (forall x₁₅: int, i₁₄: int ::
                                    (  x₁₅ == i₁₄
                                      && 0 <= i₁₄
                                      && i₁₄ < i₂₉
                                       ==> (exists i₁₄: int ::
                                              i₁₄ < 100000
                                              && x₁₅ == i₁₄
                                              && 0 <= i₁₄
                                              && i₁₄ < i₂₉
                                              && a3₂₈[x₁₅] == a1₂₅[i₁₄])))
                              && (forall x₁₅: int ::
                                      (exists i₁₄: int ::
                                              x₁₅ == i₁₄
                                              && 0 <= i₁₄
                                              && i₁₄ < i₂₉)
                                      || a3₂₈[x₁₅] == a3[x₁₅])
                              && (forall i₁₄: int ::
                                    (  0 <= i₁₄
                                      && i₁₄ < i₂₉
                                       ==> i₁₄ < 100000))
                               ==> (i₂₉ < 100000
                                   ==> 0 <= i₂₉ + 1
                                    && i₂₉ + 1 <= 100000
                                    && (forall x₁₅: int, i₁₄: int ::
                                          (  x₁₅ == i₁₄
                                            && 0 <= i₁₄
                                            && i₁₄ < i₂₉ + 1
                                             ==> (exists i₁₄: int ::
                                                    i₁₄ < 100000
                                                    && x₁₅ == i₁₄
                                                    && 0 <= i₁₄
                                                    && i₁₄ < i₂₉ + 1
                                                    && a3₂₈[i₂₉ := a1₂₅[i₂₉]][x₁₅] == a1₂₅[i₁₄])))
                                    && (forall x₁₅: int ::
                                            (exists i₁₄: int ::
                                                    x₁₅ == i₁₄
                                                    && 0 <= i₁₄
                                                    && i₁₄ < i₂₉ + 1)
                                            || a3₂₈[i₂₉ := a1₂₅[i₂₉]][x₁₅] == a3[x₁₅])
                                    && (forall i₁₄: int ::
                                          (  0 <= i₁₄
                                            && i₁₄ < i₂₉ + 1
                                             ==> i₁₄ < 100000)))
                                &&   i₂₉ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₁₉: int, i₁₈: int ::
                                          (  x₁₉ == i₁₈
                                            && 0 <= i₁₈
                                            && i₁₈ < 0
                                             ==> (exists i₁₈: int ::
                                                    i₁₈ < 100000
                                                    && x₁₉ == i₁₈
                                                    && 0 <= i₁₈
                                                    && i₁₈ < 0
                                                    && a3₂₈[x₁₉] == a2₂₆[i₁₈])))
                                    && (forall x₁₉: int ::
                                            (exists i₁₈: int ::
                                                    x₁₉ == i₁₈
                                                    && 0 <= i₁₈
                                                    && i₁₈ < 0)
                                            || a3₂₈[x₁₉] == a3₂₈[x₁₉])
                                    && (forall i₁₈: int ::
                                          (  0 <= i₁₈
                                            && i₁₈ < 0
                                             ==> i₁₈ < 100000))
                                    && (forall a3₃₀: [int]int, i₃₁: int ::
                                          (  0 <= i₃₁
                                            && i₃₁ <= 100000
                                            && (forall x₁₉: int, i₁₈: int ::
                                                  (  x₁₉ == i₁₈
                                                    && 0 <= i₁₈
                                                    && i₁₈ < i₃₁
                                                     ==> (exists i₁₈: int ::
                                                            i₁₈ < 100000
                                                            && x₁₉ == i₁₈
                                                            && 0 <= i₁₈
                                                            && i₁₈ < i₃₁
                                                            && a3₃₀[x₁₉] == a2₂₆[i₁₈])))
                                            && (forall x₁₉: int ::
                                                    (exists i₁₈: int ::
                                                            x₁₉ == i₁₈
                                                            && 0 <= i₁₈
                                                            && i₁₈ < i₃₁)
                                                    || a3₃₀[x₁₉] == a3₂₈[x₁₉])
                                            && (forall i₁₈: int ::
                                                  (  0 <= i₁₈
                                                    && i₁₈ < i₃₁
                                                     ==> i₁₈ < 100000))
                                             ==> (i₃₁ < 100000
                                                 ==> 0 <= i₃₁ + 1
                                                  && i₃₁ + 1 <= 100000
                                                  && (forall x₁₉: int, i₁₈: int ::
                                                        (  x₁₉ == i₁₈
                                                          && 0 <= i₁₈
                                                          && i₁₈ < i₃₁ + 1
                                                           ==> (exists i₁₈: int ::
                                                                  i₁₈ < 100000
                                                                  && x₁₉ == i₁₈
                                                                  && 0 <= i₁₈
                                                                  && i₁₈ < i₃₁ + 1
                                                                  && a3₃₀[i₃₁ := a2₂₆[i₃₁]][x₁₉] == a2₂₆[i₁₈])))
                                                  && (forall x₁₉: int ::
                                                          (exists i₁₈: int ::
                                                                  x₁₉ == i₁₈
                                                                  && 0 <= i₁₈
                                                                  && i₁₈ < i₃₁ + 1)
                                                          || a3₃₀[i₃₁ := a2₂₆[i₃₁]][x₁₉] == a3₂₈[x₁₉])
                                                  && (forall i₁₈: int ::
                                                        (  0 <= i₁₈
                                                          && i₁₈ < i₃₁ + 1
                                                           ==> i₁₈ < 100000)))
                                              &&   i₃₁ < 100000
                                                ||   0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₂₃: int ::
                                                        (  0 <= x₂₃
                                                          && x₂₃ < 0
                                                           ==> x₂₃ < 100000))
                                                  && (forall x₃₂: int ::
                                                        (  0 <= x₃₂
                                                          && x₃₂ <= 100000
                                                          && (forall x₂₃: int ::
                                                                (  0 <= x₂₃
                                                                  && x₂₃ < x₃₂
                                                                   ==> x₂₃ < 100000))
                                                           ==> (x₃₂ < 100000
                                                             ==> a1₂₅[x₃₂] == a3₃₀[x₃₂]
                                                              && 0 <= x₃₂ + 1
                                                              && x₃₂ + 1 <= 100000
                                                              && (forall x₂₃: int ::
                                                                    (  0 <= x₂₃
                                                                      && x₂₃ < x₃₂ + 1
                                                                       ==> x₂₃ < 100000))))))))))));


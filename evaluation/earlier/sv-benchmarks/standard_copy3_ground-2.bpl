data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int, a3: [int]int, a4: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₉: int, a₈: int ::
              (  x₉ == a₈
                && 0 <= a₈
                && a₈ < 0
                 ==> (exists __VERIFIER_nondet_int₁₆: int, a₈: int ::
                        a₈ < 100000
                        && x₉ == a₈
                        && 0 <= a₈
                        && a₈ < 0
                        && a1[x₉] == __VERIFIER_nondet_int₁₆)))
        && (forall x₉: int ::
                (exists a₈: int ::
                        x₉ == a₈
                        && 0 <= a₈
                        && a₈ < 0)
                || a1[x₉] == a1[x₉])
        && (forall x₁₀: int, a₈: int ::
              (  x₁₀ == a₈
                && 0 <= a₈
                && a₈ < 0
                 ==> (exists __VERIFIER_nondet_int₂₇: int, a₈: int ::
                        a₈ < 100000
                        && x₁₀ == a₈
                        && 0 <= a₈
                        && a₈ < 0
                        && a3[x₁₀] == __VERIFIER_nondet_int₂₇)))
        && (forall x₁₀: int ::
                (exists a₈: int ::
                        x₁₀ == a₈
                        && 0 <= a₈
                        && a₈ < 0)
                || a3[x₁₀] == a3[x₁₀])
        && (forall a₈: int ::
              (  0 <= a₈
                && a₈ < 0
                 ==> a₈ < 100000))
        && (forall a1₃₀: [int]int, a3₃₁: [int]int, a₃₂: int ::
              (  0 <= a₃₂
                && a₃₂ <= 100000
                && (forall x₉: int, a₈: int ::
                      (  x₉ == a₈
                        && 0 <= a₈
                        && a₈ < a₃₂
                         ==> (exists __VERIFIER_nondet_int₁₆: int, a₈: int ::
                                a₈ < 100000
                                && x₉ == a₈
                                && 0 <= a₈
                                && a₈ < a₃₂
                                && a1₃₀[x₉] == __VERIFIER_nondet_int₁₆)))
                && (forall x₉: int ::
                        (exists a₈: int ::
                                x₉ == a₈
                                && 0 <= a₈
                                && a₈ < a₃₂)
                        || a1₃₀[x₉] == a1[x₉])
                && (forall x₁₀: int, a₈: int ::
                      (  x₁₀ == a₈
                        && 0 <= a₈
                        && a₈ < a₃₂
                         ==> (exists __VERIFIER_nondet_int₂₇: int, a₈: int ::
                                a₈ < 100000
                                && x₁₀ == a₈
                                && 0 <= a₈
                                && a₈ < a₃₂
                                && a3₃₁[x₁₀] == __VERIFIER_nondet_int₂₇)))
                && (forall x₁₀: int ::
                        (exists a₈: int ::
                                x₁₀ == a₈
                                && 0 <= a₈
                                && a₈ < a₃₂)
                        || a3₃₁[x₁₀] == a3[x₁₀])
                && (forall a₈: int ::
                      (  0 <= a₈
                        && a₈ < a₃₂
                         ==> a₈ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (a₃₂ < 100000
                           ==> 0 <= a₃₂ + 1
                            && a₃₂ + 1 <= 100000
                            && (forall x₉: int, a₈: int ::
                                  (  x₉ == a₈
                                    && 0 <= a₈
                                    && a₈ < a₃₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₆: int, a₈: int ::
                                            a₈ < 100000
                                            && x₉ == a₈
                                            && 0 <= a₈
                                            && a₈ < a₃₂ + 1
                                            && a1₃₀[a₃₂ := __VERIFIER_nondet_int₁][x₉] == __VERIFIER_nondet_int₁₆)))
                            && (forall x₉: int ::
                                    (exists a₈: int ::
                                            x₉ == a₈
                                            && 0 <= a₈
                                            && a₈ < a₃₂ + 1)
                                    || a1₃₀[a₃₂ := __VERIFIER_nondet_int₁][x₉] == a1[x₉])
                            && (forall x₁₀: int, a₈: int ::
                                  (  x₁₀ == a₈
                                    && 0 <= a₈
                                    && a₈ < a₃₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₇: int, a₈: int ::
                                            a₈ < 100000
                                            && x₁₀ == a₈
                                            && 0 <= a₈
                                            && a₈ < a₃₂ + 1
                                            && a3₃₁[a₃₂ := __VERIFIER_nondet_int₂][x₁₀] == __VERIFIER_nondet_int₂₇)))
                            && (forall x₁₀: int ::
                                    (exists a₈: int ::
                                            x₁₀ == a₈
                                            && 0 <= a₈
                                            && a₈ < a₃₂ + 1)
                                    || a3₃₁[a₃₂ := __VERIFIER_nondet_int₂][x₁₀] == a3[x₁₀])
                            && (forall a₈: int ::
                                  (  0 <= a₈
                                    && a₈ < a₃₂ + 1
                                     ==> a₈ < 100000))))
                  &&   a₃₂ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₁₆: int, i₁₅: int ::
                            (  x₁₆ == i₁₅
                              && 0 <= i₁₅
                              && i₁₅ < 0
                               ==> (exists i₁₅: int ::
                                      i₁₅ < 100000
                                      && x₁₆ == i₁₅
                                      && 0 <= i₁₅
                                      && i₁₅ < 0
                                      && a2[x₁₆] == a1₃₀[i₁₅])))
                      && (forall x₁₆: int ::
                              (exists i₁₅: int ::
                                      x₁₆ == i₁₅
                                      && 0 <= i₁₅
                                      && i₁₅ < 0)
                              || a2[x₁₆] == a2[x₁₆])
                      && (forall i₁₅: int ::
                            (  0 <= i₁₅
                              && i₁₅ < 0
                               ==> i₁₅ < 100000))
                      && (forall a2₃₃: [int]int, i₃₄: int ::
                            (  0 <= i₃₄
                              && i₃₄ <= 100000
                              && (forall x₁₆: int, i₁₅: int ::
                                    (  x₁₆ == i₁₅
                                      && 0 <= i₁₅
                                      && i₁₅ < i₃₄
                                       ==> (exists i₁₅: int ::
                                              i₁₅ < 100000
                                              && x₁₆ == i₁₅
                                              && 0 <= i₁₅
                                              && i₁₅ < i₃₄
                                              && a2₃₃[x₁₆] == a1₃₀[i₁₅])))
                              && (forall x₁₆: int ::
                                      (exists i₁₅: int ::
                                              x₁₆ == i₁₅
                                              && 0 <= i₁₅
                                              && i₁₅ < i₃₄)
                                      || a2₃₃[x₁₆] == a2[x₁₆])
                              && (forall i₁₅: int ::
                                    (  0 <= i₁₅
                                      && i₁₅ < i₃₄
                                       ==> i₁₅ < 100000))
                               ==> (i₃₄ < 100000
                                   ==> 0 <= i₃₄ + 1
                                    && i₃₄ + 1 <= 100000
                                    && (forall x₁₆: int, i₁₅: int ::
                                          (  x₁₆ == i₁₅
                                            && 0 <= i₁₅
                                            && i₁₅ < i₃₄ + 1
                                             ==> (exists i₁₅: int ::
                                                    i₁₅ < 100000
                                                    && x₁₆ == i₁₅
                                                    && 0 <= i₁₅
                                                    && i₁₅ < i₃₄ + 1
                                                    && a2₃₃[i₃₄ := a1₃₀[i₃₄]][x₁₆] == a1₃₀[i₁₅])))
                                    && (forall x₁₆: int ::
                                            (exists i₁₅: int ::
                                                    x₁₆ == i₁₅
                                                    && 0 <= i₁₅
                                                    && i₁₅ < i₃₄ + 1)
                                            || a2₃₃[i₃₄ := a1₃₀[i₃₄]][x₁₆] == a2[x₁₆])
                                    && (forall i₁₅: int ::
                                          (  0 <= i₁₅
                                            && i₁₅ < i₃₄ + 1
                                             ==> i₁₅ < 100000)))
                                &&   i₃₄ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₂₀: int, i₁₉: int ::
                                          (  x₂₀ == i₁₉
                                            && 0 <= i₁₉
                                            && i₁₉ < 0
                                             ==> (exists i₁₉: int ::
                                                    i₁₉ < 100000
                                                    && x₂₀ == i₁₉
                                                    && 0 <= i₁₉
                                                    && i₁₉ < 0
                                                    && a4[x₂₀] == a2₃₃[i₁₉])))
                                    && (forall x₂₀: int ::
                                            (exists i₁₉: int ::
                                                    x₂₀ == i₁₉
                                                    && 0 <= i₁₉
                                                    && i₁₉ < 0)
                                            || a4[x₂₀] == a4[x₂₀])
                                    && (forall i₁₉: int ::
                                          (  0 <= i₁₉
                                            && i₁₉ < 0
                                             ==> i₁₉ < 100000))
                                    && (forall a4₃₅: [int]int, i₃₆: int ::
                                          (  0 <= i₃₆
                                            && i₃₆ <= 100000
                                            && (forall x₂₀: int, i₁₉: int ::
                                                  (  x₂₀ == i₁₉
                                                    && 0 <= i₁₉
                                                    && i₁₉ < i₃₆
                                                     ==> (exists i₁₉: int ::
                                                            i₁₉ < 100000
                                                            && x₂₀ == i₁₉
                                                            && 0 <= i₁₉
                                                            && i₁₉ < i₃₆
                                                            && a4₃₅[x₂₀] == a2₃₃[i₁₉])))
                                            && (forall x₂₀: int ::
                                                    (exists i₁₉: int ::
                                                            x₂₀ == i₁₉
                                                            && 0 <= i₁₉
                                                            && i₁₉ < i₃₆)
                                                    || a4₃₅[x₂₀] == a4[x₂₀])
                                            && (forall i₁₉: int ::
                                                  (  0 <= i₁₉
                                                    && i₁₉ < i₃₆
                                                     ==> i₁₉ < 100000))
                                             ==> (i₃₆ < 100000
                                                 ==> 0 <= i₃₆ + 1
                                                  && i₃₆ + 1 <= 100000
                                                  && (forall x₂₀: int, i₁₉: int ::
                                                        (  x₂₀ == i₁₉
                                                          && 0 <= i₁₉
                                                          && i₁₉ < i₃₆ + 1
                                                           ==> (exists i₁₉: int ::
                                                                  i₁₉ < 100000
                                                                  && x₂₀ == i₁₉
                                                                  && 0 <= i₁₉
                                                                  && i₁₉ < i₃₆ + 1
                                                                  && a4₃₅[i₃₆ := a2₃₃[i₃₆]][x₂₀] == a2₃₃[i₁₉])))
                                                  && (forall x₂₀: int ::
                                                          (exists i₁₉: int ::
                                                                  x₂₀ == i₁₉
                                                                  && 0 <= i₁₉
                                                                  && i₁₉ < i₃₆ + 1)
                                                          || a4₃₅[i₃₆ := a2₃₃[i₃₆]][x₂₀] == a4[x₂₀])
                                                  && (forall i₁₉: int ::
                                                        (  0 <= i₁₉
                                                          && i₁₉ < i₃₆ + 1
                                                           ==> i₁₉ < 100000)))
                                              &&   i₃₆ < 100000
                                                ||   0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₂₄: int, i₂₃: int ::
                                                        (  x₂₄ == i₂₃
                                                          && 0 <= i₂₃
                                                          && i₂₃ < 0
                                                           ==> (exists i₂₃: int ::
                                                                  i₂₃ < 100000
                                                                  && x₂₄ == i₂₃
                                                                  && 0 <= i₂₃
                                                                  && i₂₃ < 0
                                                                  && a4₃₅[x₂₄] == a3₃₁[i₂₃])))
                                                  && (forall x₂₄: int ::
                                                          (exists i₂₃: int ::
                                                                  x₂₄ == i₂₃
                                                                  && 0 <= i₂₃
                                                                  && i₂₃ < 0)
                                                          || a4₃₅[x₂₄] == a4₃₅[x₂₄])
                                                  && (forall i₂₃: int ::
                                                        (  0 <= i₂₃
                                                          && i₂₃ < 0
                                                           ==> i₂₃ < 100000))
                                                  && (forall a4₃₇: [int]int, i₃₈: int ::
                                                        (  0 <= i₃₈
                                                          && i₃₈ <= 100000
                                                          && (forall x₂₄: int, i₂₃: int ::
                                                                (  x₂₄ == i₂₃
                                                                  && 0 <= i₂₃
                                                                  && i₂₃ < i₃₈
                                                                   ==> (exists i₂₃: int ::
                                                                          i₂₃ < 100000
                                                                          && x₂₄ == i₂₃
                                                                          && 0 <= i₂₃
                                                                          && i₂₃ < i₃₈
                                                                          && a4₃₇[x₂₄] == a3₃₁[i₂₃])))
                                                          && (forall x₂₄: int ::
                                                                  (exists i₂₃: int ::
                                                                          x₂₄ == i₂₃
                                                                          && 0 <= i₂₃
                                                                          && i₂₃ < i₃₈)
                                                                  || a4₃₇[x₂₄] == a4₃₅[x₂₄])
                                                          && (forall i₂₃: int ::
                                                                (  0 <= i₂₃
                                                                  && i₂₃ < i₃₈
                                                                   ==> i₂₃ < 100000))
                                                           ==> (i₃₈ < 100000
                                                               ==> 0 <= i₃₈ + 1
                                                                && i₃₈ + 1 <= 100000
                                                                && (forall x₂₄: int, i₂₃: int ::
                                                                      (  x₂₄ == i₂₃
                                                                        && 0 <= i₂₃
                                                                        && i₂₃ < i₃₈ + 1
                                                                         ==> (exists i₂₃: int ::
                                                                                i₂₃ < 100000
                                                                                && x₂₄ == i₂₃
                                                                                && 0 <= i₂₃
                                                                                && i₂₃ < i₃₈ + 1
                                                                                && a4₃₇[i₃₈ := a3₃₁[i₃₈]][x₂₄] == a3₃₁[i₂₃])))
                                                                && (forall x₂₄: int ::
                                                                        (exists i₂₃: int ::
                                                                                x₂₄ == i₂₃
                                                                                && 0 <= i₂₃
                                                                                && i₂₃ < i₃₈ + 1)
                                                                        || a4₃₇[i₃₈ := a3₃₁[i₃₈]][x₂₄] == a4₃₅[x₂₄])
                                                                && (forall i₂₃: int ::
                                                                      (  0 <= i₂₃
                                                                        && i₂₃ < i₃₈ + 1
                                                                         ==> i₂₃ < 100000)))
                                                            &&   i₃₈ < 100000
                                                              ||   0 <= 0
                                                                && 0 <= 100000
                                                                && (forall x₂₈: int ::
                                                                      (  0 <= x₂₈
                                                                        && x₂₈ < 0
                                                                         ==> x₂₈ < 100000))
                                                                && (forall x₃₉: int ::
                                                                      (  0 <= x₃₉
                                                                        && x₃₉ <= 100000
                                                                        && (forall x₂₈: int ::
                                                                              (  0 <= x₂₈
                                                                                && x₂₈ < x₃₉
                                                                                 ==> x₂₈ < 100000))
                                                                         ==> (x₃₉ < 100000
                                                                           ==> a1₃₀[x₃₉] == a4₃₇[x₃₉]
                                                                            && 0 <= x₃₉ + 1
                                                                            && x₃₉ + 1 <= 100000
                                                                            && (forall x₂₈: int ::
                                                                                  (  0 <= x₂₈
                                                                                    && x₂₈ < x₃₉ + 1
                                                                                     ==> x₂₈ < 100000))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int, a3: [int]int, a4: [int]int, a5: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₁₀: int, a₉: int ::
              (  x₁₀ == a₉
                && 0 <= a₉
                && a₉ < 0
                 ==> (exists __VERIFIER_nondet_int₁₇: int, a₉: int ::
                        a₉ < 100000
                        && x₁₀ == a₉
                        && 0 <= a₉
                        && a₉ < 0
                        && a1[x₁₀] == __VERIFIER_nondet_int₁₇)))
        && (forall x₁₀: int ::
                (exists a₉: int ::
                        x₁₀ == a₉
                        && 0 <= a₉
                        && a₉ < 0)
                || a1[x₁₀] == a1[x₁₀])
        && (forall x₁₁: int, a₉: int ::
              (  x₁₁ == a₉
                && 0 <= a₉
                && a₉ < 0
                 ==> (exists __VERIFIER_nondet_int₂₈: int, a₉: int ::
                        a₉ < 100000
                        && x₁₁ == a₉
                        && 0 <= a₉
                        && a₉ < 0
                        && a4[x₁₁] == __VERIFIER_nondet_int₂₈)))
        && (forall x₁₁: int ::
                (exists a₉: int ::
                        x₁₁ == a₉
                        && 0 <= a₉
                        && a₉ < 0)
                || a4[x₁₁] == a4[x₁₁])
        && (forall a₉: int ::
              (  0 <= a₉
                && a₉ < 0
                 ==> a₉ < 100000))
        && (forall a1₃₅: [int]int, a4₃₆: [int]int, a₃₇: int ::
              (  0 <= a₃₇
                && a₃₇ <= 100000
                && (forall x₁₀: int, a₉: int ::
                      (  x₁₀ == a₉
                        && 0 <= a₉
                        && a₉ < a₃₇
                         ==> (exists __VERIFIER_nondet_int₁₇: int, a₉: int ::
                                a₉ < 100000
                                && x₁₀ == a₉
                                && 0 <= a₉
                                && a₉ < a₃₇
                                && a1₃₅[x₁₀] == __VERIFIER_nondet_int₁₇)))
                && (forall x₁₀: int ::
                        (exists a₉: int ::
                                x₁₀ == a₉
                                && 0 <= a₉
                                && a₉ < a₃₇)
                        || a1₃₅[x₁₀] == a1[x₁₀])
                && (forall x₁₁: int, a₉: int ::
                      (  x₁₁ == a₉
                        && 0 <= a₉
                        && a₉ < a₃₇
                         ==> (exists __VERIFIER_nondet_int₂₈: int, a₉: int ::
                                a₉ < 100000
                                && x₁₁ == a₉
                                && 0 <= a₉
                                && a₉ < a₃₇
                                && a4₃₆[x₁₁] == __VERIFIER_nondet_int₂₈)))
                && (forall x₁₁: int ::
                        (exists a₉: int ::
                                x₁₁ == a₉
                                && 0 <= a₉
                                && a₉ < a₃₇)
                        || a4₃₆[x₁₁] == a4[x₁₁])
                && (forall a₉: int ::
                      (  0 <= a₉
                        && a₉ < a₃₇
                         ==> a₉ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (a₃₇ < 100000
                           ==> 0 <= a₃₇ + 1
                            && a₃₇ + 1 <= 100000
                            && (forall x₁₀: int, a₉: int ::
                                  (  x₁₀ == a₉
                                    && 0 <= a₉
                                    && a₉ < a₃₇ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₇: int, a₉: int ::
                                            a₉ < 100000
                                            && x₁₀ == a₉
                                            && 0 <= a₉
                                            && a₉ < a₃₇ + 1
                                            && a1₃₅[a₃₇ := __VERIFIER_nondet_int₁][x₁₀] == __VERIFIER_nondet_int₁₇)))
                            && (forall x₁₀: int ::
                                    (exists a₉: int ::
                                            x₁₀ == a₉
                                            && 0 <= a₉
                                            && a₉ < a₃₇ + 1)
                                    || a1₃₅[a₃₇ := __VERIFIER_nondet_int₁][x₁₀] == a1[x₁₀])
                            && (forall x₁₁: int, a₉: int ::
                                  (  x₁₁ == a₉
                                    && 0 <= a₉
                                    && a₉ < a₃₇ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₈: int, a₉: int ::
                                            a₉ < 100000
                                            && x₁₁ == a₉
                                            && 0 <= a₉
                                            && a₉ < a₃₇ + 1
                                            && a4₃₆[a₃₇ := __VERIFIER_nondet_int₂][x₁₁] == __VERIFIER_nondet_int₂₈)))
                            && (forall x₁₁: int ::
                                    (exists a₉: int ::
                                            x₁₁ == a₉
                                            && 0 <= a₉
                                            && a₉ < a₃₇ + 1)
                                    || a4₃₆[a₃₇ := __VERIFIER_nondet_int₂][x₁₁] == a4[x₁₁])
                            && (forall a₉: int ::
                                  (  0 <= a₉
                                    && a₉ < a₃₇ + 1
                                     ==> a₉ < 100000))))
                  &&   a₃₇ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₁₇: int, i₁₆: int ::
                            (  x₁₇ == i₁₆
                              && 0 <= i₁₆
                              && i₁₆ < 0
                               ==> (exists i₁₆: int ::
                                      i₁₆ < 100000
                                      && x₁₇ == i₁₆
                                      && 0 <= i₁₆
                                      && i₁₆ < 0
                                      && a2[x₁₇] == a1₃₅[i₁₆])))
                      && (forall x₁₇: int ::
                              (exists i₁₆: int ::
                                      x₁₇ == i₁₆
                                      && 0 <= i₁₆
                                      && i₁₆ < 0)
                              || a2[x₁₇] == a2[x₁₇])
                      && (forall i₁₆: int ::
                            (  0 <= i₁₆
                              && i₁₆ < 0
                               ==> i₁₆ < 100000))
                      && (forall a2₃₈: [int]int, i₃₉: int ::
                            (  0 <= i₃₉
                              && i₃₉ <= 100000
                              && (forall x₁₇: int, i₁₆: int ::
                                    (  x₁₇ == i₁₆
                                      && 0 <= i₁₆
                                      && i₁₆ < i₃₉
                                       ==> (exists i₁₆: int ::
                                              i₁₆ < 100000
                                              && x₁₇ == i₁₆
                                              && 0 <= i₁₆
                                              && i₁₆ < i₃₉
                                              && a2₃₈[x₁₇] == a1₃₅[i₁₆])))
                              && (forall x₁₇: int ::
                                      (exists i₁₆: int ::
                                              x₁₇ == i₁₆
                                              && 0 <= i₁₆
                                              && i₁₆ < i₃₉)
                                      || a2₃₈[x₁₇] == a2[x₁₇])
                              && (forall i₁₆: int ::
                                    (  0 <= i₁₆
                                      && i₁₆ < i₃₉
                                       ==> i₁₆ < 100000))
                               ==> (i₃₉ < 100000
                                   ==> 0 <= i₃₉ + 1
                                    && i₃₉ + 1 <= 100000
                                    && (forall x₁₇: int, i₁₆: int ::
                                          (  x₁₇ == i₁₆
                                            && 0 <= i₁₆
                                            && i₁₆ < i₃₉ + 1
                                             ==> (exists i₁₆: int ::
                                                    i₁₆ < 100000
                                                    && x₁₇ == i₁₆
                                                    && 0 <= i₁₆
                                                    && i₁₆ < i₃₉ + 1
                                                    && a2₃₈[i₃₉ := a1₃₅[i₃₉]][x₁₇] == a1₃₅[i₁₆])))
                                    && (forall x₁₇: int ::
                                            (exists i₁₆: int ::
                                                    x₁₇ == i₁₆
                                                    && 0 <= i₁₆
                                                    && i₁₆ < i₃₉ + 1)
                                            || a2₃₈[i₃₉ := a1₃₅[i₃₉]][x₁₇] == a2[x₁₇])
                                    && (forall i₁₆: int ::
                                          (  0 <= i₁₆
                                            && i₁₆ < i₃₉ + 1
                                             ==> i₁₆ < 100000)))
                                &&   i₃₉ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₂₁: int, i₂₀: int ::
                                          (  x₂₁ == i₂₀
                                            && 0 <= i₂₀
                                            && i₂₀ < 0
                                             ==> (exists i₂₀: int ::
                                                    i₂₀ < 100000
                                                    && x₂₁ == i₂₀
                                                    && 0 <= i₂₀
                                                    && i₂₀ < 0
                                                    && a3[x₂₁] == a2₃₈[i₂₀])))
                                    && (forall x₂₁: int ::
                                            (exists i₂₀: int ::
                                                    x₂₁ == i₂₀
                                                    && 0 <= i₂₀
                                                    && i₂₀ < 0)
                                            || a3[x₂₁] == a3[x₂₁])
                                    && (forall i₂₀: int ::
                                          (  0 <= i₂₀
                                            && i₂₀ < 0
                                             ==> i₂₀ < 100000))
                                    && (forall a3₄₀: [int]int, i₄₁: int ::
                                          (  0 <= i₄₁
                                            && i₄₁ <= 100000
                                            && (forall x₂₁: int, i₂₀: int ::
                                                  (  x₂₁ == i₂₀
                                                    && 0 <= i₂₀
                                                    && i₂₀ < i₄₁
                                                     ==> (exists i₂₀: int ::
                                                            i₂₀ < 100000
                                                            && x₂₁ == i₂₀
                                                            && 0 <= i₂₀
                                                            && i₂₀ < i₄₁
                                                            && a3₄₀[x₂₁] == a2₃₈[i₂₀])))
                                            && (forall x₂₁: int ::
                                                    (exists i₂₀: int ::
                                                            x₂₁ == i₂₀
                                                            && 0 <= i₂₀
                                                            && i₂₀ < i₄₁)
                                                    || a3₄₀[x₂₁] == a3[x₂₁])
                                            && (forall i₂₀: int ::
                                                  (  0 <= i₂₀
                                                    && i₂₀ < i₄₁
                                                     ==> i₂₀ < 100000))
                                             ==> (i₄₁ < 100000
                                                 ==> 0 <= i₄₁ + 1
                                                  && i₄₁ + 1 <= 100000
                                                  && (forall x₂₁: int, i₂₀: int ::
                                                        (  x₂₁ == i₂₀
                                                          && 0 <= i₂₀
                                                          && i₂₀ < i₄₁ + 1
                                                           ==> (exists i₂₀: int ::
                                                                  i₂₀ < 100000
                                                                  && x₂₁ == i₂₀
                                                                  && 0 <= i₂₀
                                                                  && i₂₀ < i₄₁ + 1
                                                                  && a3₄₀[i₄₁ := a2₃₈[i₄₁]][x₂₁] == a2₃₈[i₂₀])))
                                                  && (forall x₂₁: int ::
                                                          (exists i₂₀: int ::
                                                                  x₂₁ == i₂₀
                                                                  && 0 <= i₂₀
                                                                  && i₂₀ < i₄₁ + 1)
                                                          || a3₄₀[i₄₁ := a2₃₈[i₄₁]][x₂₁] == a3[x₂₁])
                                                  && (forall i₂₀: int ::
                                                        (  0 <= i₂₀
                                                          && i₂₀ < i₄₁ + 1
                                                           ==> i₂₀ < 100000)))
                                              &&   i₄₁ < 100000
                                                ||   0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₂₅: int, i₂₄: int ::
                                                        (  x₂₅ == i₂₄
                                                          && 0 <= i₂₄
                                                          && i₂₄ < 0
                                                           ==> (exists i₂₄: int ::
                                                                  i₂₄ < 100000
                                                                  && x₂₅ == i₂₄
                                                                  && 0 <= i₂₄
                                                                  && i₂₄ < 0
                                                                  && a5[x₂₅] == a3₄₀[i₂₄])))
                                                  && (forall x₂₅: int ::
                                                          (exists i₂₄: int ::
                                                                  x₂₅ == i₂₄
                                                                  && 0 <= i₂₄
                                                                  && i₂₄ < 0)
                                                          || a5[x₂₅] == a5[x₂₅])
                                                  && (forall i₂₄: int ::
                                                        (  0 <= i₂₄
                                                          && i₂₄ < 0
                                                           ==> i₂₄ < 100000))
                                                  && (forall a5₄₂: [int]int, i₄₃: int ::
                                                        (  0 <= i₄₃
                                                          && i₄₃ <= 100000
                                                          && (forall x₂₅: int, i₂₄: int ::
                                                                (  x₂₅ == i₂₄
                                                                  && 0 <= i₂₄
                                                                  && i₂₄ < i₄₃
                                                                   ==> (exists i₂₄: int ::
                                                                          i₂₄ < 100000
                                                                          && x₂₅ == i₂₄
                                                                          && 0 <= i₂₄
                                                                          && i₂₄ < i₄₃
                                                                          && a5₄₂[x₂₅] == a3₄₀[i₂₄])))
                                                          && (forall x₂₅: int ::
                                                                  (exists i₂₄: int ::
                                                                          x₂₅ == i₂₄
                                                                          && 0 <= i₂₄
                                                                          && i₂₄ < i₄₃)
                                                                  || a5₄₂[x₂₅] == a5[x₂₅])
                                                          && (forall i₂₄: int ::
                                                                (  0 <= i₂₄
                                                                  && i₂₄ < i₄₃
                                                                   ==> i₂₄ < 100000))
                                                           ==> (i₄₃ < 100000
                                                               ==> 0 <= i₄₃ + 1
                                                                && i₄₃ + 1 <= 100000
                                                                && (forall x₂₅: int, i₂₄: int ::
                                                                      (  x₂₅ == i₂₄
                                                                        && 0 <= i₂₄
                                                                        && i₂₄ < i₄₃ + 1
                                                                         ==> (exists i₂₄: int ::
                                                                                i₂₄ < 100000
                                                                                && x₂₅ == i₂₄
                                                                                && 0 <= i₂₄
                                                                                && i₂₄ < i₄₃ + 1
                                                                                && a5₄₂[i₄₃ := a3₄₀[i₄₃]][x₂₅] == a3₄₀[i₂₄])))
                                                                && (forall x₂₅: int ::
                                                                        (exists i₂₄: int ::
                                                                                x₂₅ == i₂₄
                                                                                && 0 <= i₂₄
                                                                                && i₂₄ < i₄₃ + 1)
                                                                        || a5₄₂[i₄₃ := a3₄₀[i₄₃]][x₂₅] == a5[x₂₅])
                                                                && (forall i₂₄: int ::
                                                                      (  0 <= i₂₄
                                                                        && i₂₄ < i₄₃ + 1
                                                                         ==> i₂₄ < 100000)))
                                                            &&   i₄₃ < 100000
                                                              ||   0 <= 0
                                                                && 0 <= 100000
                                                                && (forall x₂₉: int, i₂₈: int ::
                                                                      (  x₂₉ == i₂₈
                                                                        && 0 <= i₂₈
                                                                        && i₂₈ < 0
                                                                         ==> (exists i₂₈: int ::
                                                                                i₂₈ < 100000
                                                                                && x₂₉ == i₂₈
                                                                                && 0 <= i₂₈
                                                                                && i₂₈ < 0
                                                                                && a5₄₂[x₂₉] == a4₃₆[i₂₈])))
                                                                && (forall x₂₉: int ::
                                                                        (exists i₂₈: int ::
                                                                                x₂₉ == i₂₈
                                                                                && 0 <= i₂₈
                                                                                && i₂₈ < 0)
                                                                        || a5₄₂[x₂₉] == a5₄₂[x₂₉])
                                                                && (forall i₂₈: int ::
                                                                      (  0 <= i₂₈
                                                                        && i₂₈ < 0
                                                                         ==> i₂₈ < 100000))
                                                                && (forall a5₄₄: [int]int, i₄₅: int ::
                                                                      (  0 <= i₄₅
                                                                        && i₄₅ <= 100000
                                                                        && (forall x₂₉: int, i₂₈: int ::
                                                                              (  x₂₉ == i₂₈
                                                                                && 0 <= i₂₈
                                                                                && i₂₈ < i₄₅
                                                                                 ==> (exists i₂₈: int ::
                                                                                        i₂₈ < 100000
                                                                                        && x₂₉ == i₂₈
                                                                                        && 0 <= i₂₈
                                                                                        && i₂₈ < i₄₅
                                                                                        && a5₄₄[x₂₉] == a4₃₆[i₂₈])))
                                                                        && (forall x₂₉: int ::
                                                                                (exists i₂₈: int ::
                                                                                        x₂₉ == i₂₈
                                                                                        && 0 <= i₂₈
                                                                                        && i₂₈ < i₄₅)
                                                                                || a5₄₄[x₂₉] == a5₄₂[x₂₉])
                                                                        && (forall i₂₈: int ::
                                                                              (  0 <= i₂₈
                                                                                && i₂₈ < i₄₅
                                                                                 ==> i₂₈ < 100000))
                                                                         ==> (i₄₅ < 100000
                                                                             ==> 0 <= i₄₅ + 1
                                                                              && i₄₅ + 1 <= 100000
                                                                              && (forall x₂₉: int, i₂₈: int ::
                                                                                    (  x₂₉ == i₂₈
                                                                                      && 0 <= i₂₈
                                                                                      && i₂₈ < i₄₅ + 1
                                                                                       ==> (exists i₂₈: int ::
                                                                                              i₂₈ < 100000
                                                                                              && x₂₉ == i₂₈
                                                                                              && 0 <= i₂₈
                                                                                              && i₂₈ < i₄₅ + 1
                                                                                              && a5₄₄[i₄₅ := a4₃₆[i₄₅]][x₂₉] == a4₃₆[i₂₈])))
                                                                              && (forall x₂₉: int ::
                                                                                      (exists i₂₈: int ::
                                                                                              x₂₉ == i₂₈
                                                                                              && 0 <= i₂₈
                                                                                              && i₂₈ < i₄₅ + 1)
                                                                                      || a5₄₄[i₄₅ := a4₃₆[i₄₅]][x₂₉] == a5₄₂[x₂₉])
                                                                              && (forall i₂₈: int ::
                                                                                    (  0 <= i₂₈
                                                                                      && i₂₈ < i₄₅ + 1
                                                                                       ==> i₂₈ < 100000)))
                                                                          &&   i₄₅ < 100000
                                                                            ||   0 <= 0
                                                                              && 0 <= 100000
                                                                              && (forall x₃₃: int ::
                                                                                    (  0 <= x₃₃
                                                                                      && x₃₃ < 0
                                                                                       ==> x₃₃ < 100000))
                                                                              && (forall x₄₆: int ::
                                                                                    (  0 <= x₄₆
                                                                                      && x₄₆ <= 100000
                                                                                      && (forall x₃₃: int ::
                                                                                            (  0 <= x₃₃
                                                                                              && x₃₃ < x₄₆
                                                                                               ==> x₃₃ < 100000))
                                                                                       ==> (x₄₆ < 100000
                                                                                         ==> a1₃₅[x₄₆] == a5₄₄[x₄₆]
                                                                                          && 0 <= x₄₆ + 1
                                                                                          && x₄₆ + 1 <= 100000
                                                                                          && (forall x₃₃: int ::
                                                                                                (  0 <= x₃₃
                                                                                                  && x₃₃ < x₄₆ + 1
                                                                                                   ==> x₃₃ < 100000))))))))))))))));


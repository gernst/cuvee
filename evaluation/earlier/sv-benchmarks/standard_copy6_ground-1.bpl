data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int, a3: [int]int, a4: [int]int, a5: [int]int, a6: [int]int, a7: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₁₂: int, a₁₁: int ::
              (  x₁₂ == a₁₁
                && 0 <= a₁₁
                && a₁₁ < 0
                 ==> (exists __VERIFIER_nondet_int₁₉: int, a₁₁: int ::
                        a₁₁ < 100000
                        && x₁₂ == a₁₁
                        && 0 <= a₁₁
                        && a₁₁ < 0
                        && a1[x₁₂] == __VERIFIER_nondet_int₁₉)))
        && (forall x₁₂: int ::
                (exists a₁₁: int ::
                        x₁₂ == a₁₁
                        && 0 <= a₁₁
                        && a₁₁ < 0)
                || a1[x₁₂] == a1[x₁₂])
        && (forall x₁₃: int, a₁₁: int ::
              (  x₁₃ == a₁₁
                && 0 <= a₁₁
                && a₁₁ < 0
                 ==> (exists __VERIFIER_nondet_int₂₁₀: int, a₁₁: int ::
                        a₁₁ < 100000
                        && x₁₃ == a₁₁
                        && 0 <= a₁₁
                        && a₁₁ < 0
                        && a6[x₁₃] == __VERIFIER_nondet_int₂₁₀)))
        && (forall x₁₃: int ::
                (exists a₁₁: int ::
                        x₁₃ == a₁₁
                        && 0 <= a₁₁
                        && a₁₁ < 0)
                || a6[x₁₃] == a6[x₁₃])
        && (forall a₁₁: int ::
              (  0 <= a₁₁
                && a₁₁ < 0
                 ==> a₁₁ < 100000))
        && (forall a1₄₅: [int]int, a6₄₆: [int]int, a₄₇: int ::
              (  0 <= a₄₇
                && a₄₇ <= 100000
                && (forall x₁₂: int, a₁₁: int ::
                      (  x₁₂ == a₁₁
                        && 0 <= a₁₁
                        && a₁₁ < a₄₇
                         ==> (exists __VERIFIER_nondet_int₁₉: int, a₁₁: int ::
                                a₁₁ < 100000
                                && x₁₂ == a₁₁
                                && 0 <= a₁₁
                                && a₁₁ < a₄₇
                                && a1₄₅[x₁₂] == __VERIFIER_nondet_int₁₉)))
                && (forall x₁₂: int ::
                        (exists a₁₁: int ::
                                x₁₂ == a₁₁
                                && 0 <= a₁₁
                                && a₁₁ < a₄₇)
                        || a1₄₅[x₁₂] == a1[x₁₂])
                && (forall x₁₃: int, a₁₁: int ::
                      (  x₁₃ == a₁₁
                        && 0 <= a₁₁
                        && a₁₁ < a₄₇
                         ==> (exists __VERIFIER_nondet_int₂₁₀: int, a₁₁: int ::
                                a₁₁ < 100000
                                && x₁₃ == a₁₁
                                && 0 <= a₁₁
                                && a₁₁ < a₄₇
                                && a6₄₆[x₁₃] == __VERIFIER_nondet_int₂₁₀)))
                && (forall x₁₃: int ::
                        (exists a₁₁: int ::
                                x₁₃ == a₁₁
                                && 0 <= a₁₁
                                && a₁₁ < a₄₇)
                        || a6₄₆[x₁₃] == a6[x₁₃])
                && (forall a₁₁: int ::
                      (  0 <= a₁₁
                        && a₁₁ < a₄₇
                         ==> a₁₁ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (a₄₇ < 100000
                           ==> 0 <= a₄₇ + 1
                            && a₄₇ + 1 <= 100000
                            && (forall x₁₂: int, a₁₁: int ::
                                  (  x₁₂ == a₁₁
                                    && 0 <= a₁₁
                                    && a₁₁ < a₄₇ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₉: int, a₁₁: int ::
                                            a₁₁ < 100000
                                            && x₁₂ == a₁₁
                                            && 0 <= a₁₁
                                            && a₁₁ < a₄₇ + 1
                                            && a1₄₅[a₄₇ := __VERIFIER_nondet_int₁][x₁₂] == __VERIFIER_nondet_int₁₉)))
                            && (forall x₁₂: int ::
                                    (exists a₁₁: int ::
                                            x₁₂ == a₁₁
                                            && 0 <= a₁₁
                                            && a₁₁ < a₄₇ + 1)
                                    || a1₄₅[a₄₇ := __VERIFIER_nondet_int₁][x₁₂] == a1[x₁₂])
                            && (forall x₁₃: int, a₁₁: int ::
                                  (  x₁₃ == a₁₁
                                    && 0 <= a₁₁
                                    && a₁₁ < a₄₇ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₁₀: int, a₁₁: int ::
                                            a₁₁ < 100000
                                            && x₁₃ == a₁₁
                                            && 0 <= a₁₁
                                            && a₁₁ < a₄₇ + 1
                                            && a6₄₆[a₄₇ := __VERIFIER_nondet_int₂][x₁₃] == __VERIFIER_nondet_int₂₁₀)))
                            && (forall x₁₃: int ::
                                    (exists a₁₁: int ::
                                            x₁₃ == a₁₁
                                            && 0 <= a₁₁
                                            && a₁₁ < a₄₇ + 1)
                                    || a6₄₆[a₄₇ := __VERIFIER_nondet_int₂][x₁₃] == a6[x₁₃])
                            && (forall a₁₁: int ::
                                  (  0 <= a₁₁
                                    && a₁₁ < a₄₇ + 1
                                     ==> a₁₁ < 100000))))
                  &&   a₄₇ < 100000
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
                                      && a2[x₁₉] == a1₄₅[i₁₈])))
                      && (forall x₁₉: int ::
                              (exists i₁₈: int ::
                                      x₁₉ == i₁₈
                                      && 0 <= i₁₈
                                      && i₁₈ < 0)
                              || a2[x₁₉] == a2[x₁₉])
                      && (forall i₁₈: int ::
                            (  0 <= i₁₈
                              && i₁₈ < 0
                               ==> i₁₈ < 100000))
                      && (forall a2₄₈: [int]int, i₄₉: int ::
                            (  0 <= i₄₉
                              && i₄₉ <= 100000
                              && (forall x₁₉: int, i₁₈: int ::
                                    (  x₁₉ == i₁₈
                                      && 0 <= i₁₈
                                      && i₁₈ < i₄₉
                                       ==> (exists i₁₈: int ::
                                              i₁₈ < 100000
                                              && x₁₉ == i₁₈
                                              && 0 <= i₁₈
                                              && i₁₈ < i₄₉
                                              && a2₄₈[x₁₉] == a1₄₅[i₁₈])))
                              && (forall x₁₉: int ::
                                      (exists i₁₈: int ::
                                              x₁₉ == i₁₈
                                              && 0 <= i₁₈
                                              && i₁₈ < i₄₉)
                                      || a2₄₈[x₁₉] == a2[x₁₉])
                              && (forall i₁₈: int ::
                                    (  0 <= i₁₈
                                      && i₁₈ < i₄₉
                                       ==> i₁₈ < 100000))
                               ==> (i₄₉ < 100000
                                   ==> 0 <= i₄₉ + 1
                                    && i₄₉ + 1 <= 100000
                                    && (forall x₁₉: int, i₁₈: int ::
                                          (  x₁₉ == i₁₈
                                            && 0 <= i₁₈
                                            && i₁₈ < i₄₉ + 1
                                             ==> (exists i₁₈: int ::
                                                    i₁₈ < 100000
                                                    && x₁₉ == i₁₈
                                                    && 0 <= i₁₈
                                                    && i₁₈ < i₄₉ + 1
                                                    && a2₄₈[i₄₉ := a1₄₅[i₄₉]][x₁₉] == a1₄₅[i₁₈])))
                                    && (forall x₁₉: int ::
                                            (exists i₁₈: int ::
                                                    x₁₉ == i₁₈
                                                    && 0 <= i₁₈
                                                    && i₁₈ < i₄₉ + 1)
                                            || a2₄₈[i₄₉ := a1₄₅[i₄₉]][x₁₉] == a2[x₁₉])
                                    && (forall i₁₈: int ::
                                          (  0 <= i₁₈
                                            && i₁₈ < i₄₉ + 1
                                             ==> i₁₈ < 100000)))
                                &&   i₄₉ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₂₃: int, i₂₂: int ::
                                          (  x₂₃ == i₂₂
                                            && 0 <= i₂₂
                                            && i₂₂ < 0
                                             ==> (exists i₂₂: int ::
                                                    i₂₂ < 100000
                                                    && x₂₃ == i₂₂
                                                    && 0 <= i₂₂
                                                    && i₂₂ < 0
                                                    && a3[x₂₃] == a2₄₈[i₂₂])))
                                    && (forall x₂₃: int ::
                                            (exists i₂₂: int ::
                                                    x₂₃ == i₂₂
                                                    && 0 <= i₂₂
                                                    && i₂₂ < 0)
                                            || a3[x₂₃] == a3[x₂₃])
                                    && (forall i₂₂: int ::
                                          (  0 <= i₂₂
                                            && i₂₂ < 0
                                             ==> i₂₂ < 100000))
                                    && (forall a3₅₀: [int]int, i₅₁: int ::
                                          (  0 <= i₅₁
                                            && i₅₁ <= 100000
                                            && (forall x₂₃: int, i₂₂: int ::
                                                  (  x₂₃ == i₂₂
                                                    && 0 <= i₂₂
                                                    && i₂₂ < i₅₁
                                                     ==> (exists i₂₂: int ::
                                                            i₂₂ < 100000
                                                            && x₂₃ == i₂₂
                                                            && 0 <= i₂₂
                                                            && i₂₂ < i₅₁
                                                            && a3₅₀[x₂₃] == a2₄₈[i₂₂])))
                                            && (forall x₂₃: int ::
                                                    (exists i₂₂: int ::
                                                            x₂₃ == i₂₂
                                                            && 0 <= i₂₂
                                                            && i₂₂ < i₅₁)
                                                    || a3₅₀[x₂₃] == a3[x₂₃])
                                            && (forall i₂₂: int ::
                                                  (  0 <= i₂₂
                                                    && i₂₂ < i₅₁
                                                     ==> i₂₂ < 100000))
                                             ==> (i₅₁ < 100000
                                                 ==> 0 <= i₅₁ + 1
                                                  && i₅₁ + 1 <= 100000
                                                  && (forall x₂₃: int, i₂₂: int ::
                                                        (  x₂₃ == i₂₂
                                                          && 0 <= i₂₂
                                                          && i₂₂ < i₅₁ + 1
                                                           ==> (exists i₂₂: int ::
                                                                  i₂₂ < 100000
                                                                  && x₂₃ == i₂₂
                                                                  && 0 <= i₂₂
                                                                  && i₂₂ < i₅₁ + 1
                                                                  && a3₅₀[i₅₁ := a2₄₈[i₅₁]][x₂₃] == a2₄₈[i₂₂])))
                                                  && (forall x₂₃: int ::
                                                          (exists i₂₂: int ::
                                                                  x₂₃ == i₂₂
                                                                  && 0 <= i₂₂
                                                                  && i₂₂ < i₅₁ + 1)
                                                          || a3₅₀[i₅₁ := a2₄₈[i₅₁]][x₂₃] == a3[x₂₃])
                                                  && (forall i₂₂: int ::
                                                        (  0 <= i₂₂
                                                          && i₂₂ < i₅₁ + 1
                                                           ==> i₂₂ < 100000)))
                                              &&   i₅₁ < 100000
                                                ||   0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₂₇: int, i₂₆: int ::
                                                        (  x₂₇ == i₂₆
                                                          && 0 <= i₂₆
                                                          && i₂₆ < 0
                                                           ==> (exists i₂₆: int ::
                                                                  i₂₆ < 100000
                                                                  && x₂₇ == i₂₆
                                                                  && 0 <= i₂₆
                                                                  && i₂₆ < 0
                                                                  && a4[x₂₇] == a3₅₀[i₂₆])))
                                                  && (forall x₂₇: int ::
                                                          (exists i₂₆: int ::
                                                                  x₂₇ == i₂₆
                                                                  && 0 <= i₂₆
                                                                  && i₂₆ < 0)
                                                          || a4[x₂₇] == a4[x₂₇])
                                                  && (forall i₂₆: int ::
                                                        (  0 <= i₂₆
                                                          && i₂₆ < 0
                                                           ==> i₂₆ < 100000))
                                                  && (forall a4₅₂: [int]int, i₅₃: int ::
                                                        (  0 <= i₅₃
                                                          && i₅₃ <= 100000
                                                          && (forall x₂₇: int, i₂₆: int ::
                                                                (  x₂₇ == i₂₆
                                                                  && 0 <= i₂₆
                                                                  && i₂₆ < i₅₃
                                                                   ==> (exists i₂₆: int ::
                                                                          i₂₆ < 100000
                                                                          && x₂₇ == i₂₆
                                                                          && 0 <= i₂₆
                                                                          && i₂₆ < i₅₃
                                                                          && a4₅₂[x₂₇] == a3₅₀[i₂₆])))
                                                          && (forall x₂₇: int ::
                                                                  (exists i₂₆: int ::
                                                                          x₂₇ == i₂₆
                                                                          && 0 <= i₂₆
                                                                          && i₂₆ < i₅₃)
                                                                  || a4₅₂[x₂₇] == a4[x₂₇])
                                                          && (forall i₂₆: int ::
                                                                (  0 <= i₂₆
                                                                  && i₂₆ < i₅₃
                                                                   ==> i₂₆ < 100000))
                                                           ==> (i₅₃ < 100000
                                                               ==> 0 <= i₅₃ + 1
                                                                && i₅₃ + 1 <= 100000
                                                                && (forall x₂₇: int, i₂₆: int ::
                                                                      (  x₂₇ == i₂₆
                                                                        && 0 <= i₂₆
                                                                        && i₂₆ < i₅₃ + 1
                                                                         ==> (exists i₂₆: int ::
                                                                                i₂₆ < 100000
                                                                                && x₂₇ == i₂₆
                                                                                && 0 <= i₂₆
                                                                                && i₂₆ < i₅₃ + 1
                                                                                && a4₅₂[i₅₃ := a3₅₀[i₅₃]][x₂₇] == a3₅₀[i₂₆])))
                                                                && (forall x₂₇: int ::
                                                                        (exists i₂₆: int ::
                                                                                x₂₇ == i₂₆
                                                                                && 0 <= i₂₆
                                                                                && i₂₆ < i₅₃ + 1)
                                                                        || a4₅₂[i₅₃ := a3₅₀[i₅₃]][x₂₇] == a4[x₂₇])
                                                                && (forall i₂₆: int ::
                                                                      (  0 <= i₂₆
                                                                        && i₂₆ < i₅₃ + 1
                                                                         ==> i₂₆ < 100000)))
                                                            &&   i₅₃ < 100000
                                                              ||   0 <= 0
                                                                && 0 <= 100000
                                                                && (forall x₃₁: int, i₃₀: int ::
                                                                      (  x₃₁ == i₃₀
                                                                        && 0 <= i₃₀
                                                                        && i₃₀ < 0
                                                                         ==> (exists i₃₀: int ::
                                                                                i₃₀ < 100000
                                                                                && x₃₁ == i₃₀
                                                                                && 0 <= i₃₀
                                                                                && i₃₀ < 0
                                                                                && a5[x₃₁] == a4₅₂[i₃₀])))
                                                                && (forall x₃₁: int ::
                                                                        (exists i₃₀: int ::
                                                                                x₃₁ == i₃₀
                                                                                && 0 <= i₃₀
                                                                                && i₃₀ < 0)
                                                                        || a5[x₃₁] == a5[x₃₁])
                                                                && (forall i₃₀: int ::
                                                                      (  0 <= i₃₀
                                                                        && i₃₀ < 0
                                                                         ==> i₃₀ < 100000))
                                                                && (forall a5₅₄: [int]int, i₅₅: int ::
                                                                      (  0 <= i₅₅
                                                                        && i₅₅ <= 100000
                                                                        && (forall x₃₁: int, i₃₀: int ::
                                                                              (  x₃₁ == i₃₀
                                                                                && 0 <= i₃₀
                                                                                && i₃₀ < i₅₅
                                                                                 ==> (exists i₃₀: int ::
                                                                                        i₃₀ < 100000
                                                                                        && x₃₁ == i₃₀
                                                                                        && 0 <= i₃₀
                                                                                        && i₃₀ < i₅₅
                                                                                        && a5₅₄[x₃₁] == a4₅₂[i₃₀])))
                                                                        && (forall x₃₁: int ::
                                                                                (exists i₃₀: int ::
                                                                                        x₃₁ == i₃₀
                                                                                        && 0 <= i₃₀
                                                                                        && i₃₀ < i₅₅)
                                                                                || a5₅₄[x₃₁] == a5[x₃₁])
                                                                        && (forall i₃₀: int ::
                                                                              (  0 <= i₃₀
                                                                                && i₃₀ < i₅₅
                                                                                 ==> i₃₀ < 100000))
                                                                         ==> (i₅₅ < 100000
                                                                             ==> 0 <= i₅₅ + 1
                                                                              && i₅₅ + 1 <= 100000
                                                                              && (forall x₃₁: int, i₃₀: int ::
                                                                                    (  x₃₁ == i₃₀
                                                                                      && 0 <= i₃₀
                                                                                      && i₃₀ < i₅₅ + 1
                                                                                       ==> (exists i₃₀: int ::
                                                                                              i₃₀ < 100000
                                                                                              && x₃₁ == i₃₀
                                                                                              && 0 <= i₃₀
                                                                                              && i₃₀ < i₅₅ + 1
                                                                                              && a5₅₄[i₅₅ := a4₅₂[i₅₅]][x₃₁] == a4₅₂[i₃₀])))
                                                                              && (forall x₃₁: int ::
                                                                                      (exists i₃₀: int ::
                                                                                              x₃₁ == i₃₀
                                                                                              && 0 <= i₃₀
                                                                                              && i₃₀ < i₅₅ + 1)
                                                                                      || a5₅₄[i₅₅ := a4₅₂[i₅₅]][x₃₁] == a5[x₃₁])
                                                                              && (forall i₃₀: int ::
                                                                                    (  0 <= i₃₀
                                                                                      && i₃₀ < i₅₅ + 1
                                                                                       ==> i₃₀ < 100000)))
                                                                          &&   i₅₅ < 100000
                                                                            ||   0 <= 0
                                                                              && 0 <= 100000
                                                                              && (forall x₃₅: int, i₃₄: int ::
                                                                                    (  x₃₅ == i₃₄
                                                                                      && 0 <= i₃₄
                                                                                      && i₃₄ < 0
                                                                                       ==> (exists i₃₄: int ::
                                                                                              i₃₄ < 100000
                                                                                              && x₃₅ == i₃₄
                                                                                              && 0 <= i₃₄
                                                                                              && i₃₄ < 0
                                                                                              && a7[x₃₅] == a5₅₄[i₃₄])))
                                                                              && (forall x₃₅: int ::
                                                                                      (exists i₃₄: int ::
                                                                                              x₃₅ == i₃₄
                                                                                              && 0 <= i₃₄
                                                                                              && i₃₄ < 0)
                                                                                      || a7[x₃₅] == a7[x₃₅])
                                                                              && (forall i₃₄: int ::
                                                                                    (  0 <= i₃₄
                                                                                      && i₃₄ < 0
                                                                                       ==> i₃₄ < 100000))
                                                                              && (forall a7₅₆: [int]int, i₅₇: int ::
                                                                                    (  0 <= i₅₇
                                                                                      && i₅₇ <= 100000
                                                                                      && (forall x₃₅: int, i₃₄: int ::
                                                                                            (  x₃₅ == i₃₄
                                                                                              && 0 <= i₃₄
                                                                                              && i₃₄ < i₅₇
                                                                                               ==> (exists i₃₄: int ::
                                                                                                      i₃₄ < 100000
                                                                                                      && x₃₅ == i₃₄
                                                                                                      && 0 <= i₃₄
                                                                                                      && i₃₄ < i₅₇
                                                                                                      && a7₅₆[x₃₅] == a5₅₄[i₃₄])))
                                                                                      && (forall x₃₅: int ::
                                                                                              (exists i₃₄: int ::
                                                                                                      x₃₅ == i₃₄
                                                                                                      && 0 <= i₃₄
                                                                                                      && i₃₄ < i₅₇)
                                                                                              || a7₅₆[x₃₅] == a7[x₃₅])
                                                                                      && (forall i₃₄: int ::
                                                                                            (  0 <= i₃₄
                                                                                              && i₃₄ < i₅₇
                                                                                               ==> i₃₄ < 100000))
                                                                                       ==> (i₅₇ < 100000
                                                                                           ==> 0 <= i₅₇ + 1
                                                                                            && i₅₇ + 1 <= 100000
                                                                                            && (forall x₃₅: int, i₃₄: int ::
                                                                                                  (  x₃₅ == i₃₄
                                                                                                    && 0 <= i₃₄
                                                                                                    && i₃₄ < i₅₇ + 1
                                                                                                     ==> (exists i₃₄: int ::
                                                                                                            i₃₄ < 100000
                                                                                                            && x₃₅ == i₃₄
                                                                                                            && 0 <= i₃₄
                                                                                                            && i₃₄ < i₅₇ + 1
                                                                                                            && a7₅₆[i₅₇ := a5₅₄[i₅₇]][x₃₅] == a5₅₄[i₃₄])))
                                                                                            && (forall x₃₅: int ::
                                                                                                    (exists i₃₄: int ::
                                                                                                            x₃₅ == i₃₄
                                                                                                            && 0 <= i₃₄
                                                                                                            && i₃₄ < i₅₇ + 1)
                                                                                                    || a7₅₆[i₅₇ := a5₅₄[i₅₇]][x₃₅] == a7[x₃₅])
                                                                                            && (forall i₃₄: int ::
                                                                                                  (  0 <= i₃₄
                                                                                                    && i₃₄ < i₅₇ + 1
                                                                                                     ==> i₃₄ < 100000)))
                                                                                        &&   i₅₇ < 100000
                                                                                          ||   0 <= 0
                                                                                            && 0 <= 100000
                                                                                            && (forall x₃₉: int, i₃₈: int ::
                                                                                                  (  x₃₉ == i₃₈
                                                                                                    && 0 <= i₃₈
                                                                                                    && i₃₈ < 0
                                                                                                     ==> (exists i₃₈: int ::
                                                                                                            i₃₈ < 100000
                                                                                                            && x₃₉ == i₃₈
                                                                                                            && 0 <= i₃₈
                                                                                                            && i₃₈ < 0
                                                                                                            && a7₅₆[x₃₉] == a6₄₆[i₃₈])))
                                                                                            && (forall x₃₉: int ::
                                                                                                    (exists i₃₈: int ::
                                                                                                            x₃₉ == i₃₈
                                                                                                            && 0 <= i₃₈
                                                                                                            && i₃₈ < 0)
                                                                                                    || a7₅₆[x₃₉] == a7₅₆[x₃₉])
                                                                                            && (forall i₃₈: int ::
                                                                                                  (  0 <= i₃₈
                                                                                                    && i₃₈ < 0
                                                                                                     ==> i₃₈ < 100000))
                                                                                            && (forall a7₅₈: [int]int, i₅₉: int ::
                                                                                                  (  0 <= i₅₉
                                                                                                    && i₅₉ <= 100000
                                                                                                    && (forall x₃₉: int, i₃₈: int ::
                                                                                                          (  x₃₉ == i₃₈
                                                                                                            && 0 <= i₃₈
                                                                                                            && i₃₈ < i₅₉
                                                                                                             ==> (exists i₃₈: int ::
                                                                                                                    i₃₈ < 100000
                                                                                                                    && x₃₉ == i₃₈
                                                                                                                    && 0 <= i₃₈
                                                                                                                    && i₃₈ < i₅₉
                                                                                                                    && a7₅₈[x₃₉] == a6₄₆[i₃₈])))
                                                                                                    && (forall x₃₉: int ::
                                                                                                            (exists i₃₈: int ::
                                                                                                                    x₃₉ == i₃₈
                                                                                                                    && 0 <= i₃₈
                                                                                                                    && i₃₈ < i₅₉)
                                                                                                            || a7₅₈[x₃₉] == a7₅₆[x₃₉])
                                                                                                    && (forall i₃₈: int ::
                                                                                                          (  0 <= i₃₈
                                                                                                            && i₃₈ < i₅₉
                                                                                                             ==> i₃₈ < 100000))
                                                                                                     ==> (i₅₉ < 100000
                                                                                                         ==> 0 <= i₅₉ + 1
                                                                                                          && i₅₉ + 1 <= 100000
                                                                                                          && (forall x₃₉: int, i₃₈: int ::
                                                                                                                (  x₃₉ == i₃₈
                                                                                                                  && 0 <= i₃₈
                                                                                                                  && i₃₈ < i₅₉ + 1
                                                                                                                   ==> (exists i₃₈: int ::
                                                                                                                          i₃₈ < 100000
                                                                                                                          && x₃₉ == i₃₈
                                                                                                                          && 0 <= i₃₈
                                                                                                                          && i₃₈ < i₅₉ + 1
                                                                                                                          && a7₅₈[i₅₉ := a6₄₆[i₅₉]][x₃₉] == a6₄₆[i₃₈])))
                                                                                                          && (forall x₃₉: int ::
                                                                                                                  (exists i₃₈: int ::
                                                                                                                          x₃₉ == i₃₈
                                                                                                                          && 0 <= i₃₈
                                                                                                                          && i₃₈ < i₅₉ + 1)
                                                                                                                  || a7₅₈[i₅₉ := a6₄₆[i₅₉]][x₃₉] == a7₅₆[x₃₉])
                                                                                                          && (forall i₃₈: int ::
                                                                                                                (  0 <= i₃₈
                                                                                                                  && i₃₈ < i₅₉ + 1
                                                                                                                   ==> i₃₈ < 100000)))
                                                                                                      &&   i₅₉ < 100000
                                                                                                        ||   0 <= 0
                                                                                                          && 0 <= 100000
                                                                                                          && (forall x₄₃: int ::
                                                                                                                (  0 <= x₄₃
                                                                                                                  && x₄₃ < 0
                                                                                                                   ==> x₄₃ < 100000))
                                                                                                          && (forall x₆₀: int ::
                                                                                                                (  0 <= x₆₀
                                                                                                                  && x₆₀ <= 100000
                                                                                                                  && (forall x₄₃: int ::
                                                                                                                        (  0 <= x₄₃
                                                                                                                          && x₄₃ < x₆₀
                                                                                                                           ==> x₄₃ < 100000))
                                                                                                                   ==> (x₆₀ < 100000
                                                                                                                     ==> a1₄₅[x₆₀] == a7₅₈[x₆₀]
                                                                                                                      && 0 <= x₆₀ + 1
                                                                                                                      && x₆₀ + 1 <= 100000
                                                                                                                      && (forall x₄₃: int ::
                                                                                                                            (  0 <= x₄₃
                                                                                                                              && x₄₃ < x₆₀ + 1
                                                                                                                               ==> x₄₃ < 100000))))))))))))))))))));


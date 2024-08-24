data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int, a3: [int]int, a4: [int]int, a5: [int]int, a6: [int]int, a7: [int]int, a8: [int]int, a9: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₁₄: int, a₁₃: int ::
              (  x₁₄ == a₁₃
                && 0 <= a₁₃
                && a₁₃ < 0
                 ==> (exists __VERIFIER_nondet_int₁₁₁: int, a₁₃: int ::
                        a₁₃ < 100000
                        && x₁₄ == a₁₃
                        && 0 <= a₁₃
                        && a₁₃ < 0
                        && a1[x₁₄] == __VERIFIER_nondet_int₁₁₁)))
        && (forall x₁₄: int ::
                (exists a₁₃: int ::
                        x₁₄ == a₁₃
                        && 0 <= a₁₃
                        && a₁₃ < 0)
                || a1[x₁₄] == a1[x₁₄])
        && (forall x₁₅: int, a₁₃: int ::
              (  x₁₅ == a₁₃
                && 0 <= a₁₃
                && a₁₃ < 0
                 ==> (exists __VERIFIER_nondet_int₂₁₂: int, a₁₃: int ::
                        a₁₃ < 100000
                        && x₁₅ == a₁₃
                        && 0 <= a₁₃
                        && a₁₃ < 0
                        && a8[x₁₅] == __VERIFIER_nondet_int₂₁₂)))
        && (forall x₁₅: int ::
                (exists a₁₃: int ::
                        x₁₅ == a₁₃
                        && 0 <= a₁₃
                        && a₁₃ < 0)
                || a8[x₁₅] == a8[x₁₅])
        && (forall a₁₃: int ::
              (  0 <= a₁₃
                && a₁₃ < 0
                 ==> a₁₃ < 100000))
        && (forall a1₅₅: [int]int, a8₅₆: [int]int, a₅₇: int ::
              (  0 <= a₅₇
                && a₅₇ <= 100000
                && (forall x₁₄: int, a₁₃: int ::
                      (  x₁₄ == a₁₃
                        && 0 <= a₁₃
                        && a₁₃ < a₅₇
                         ==> (exists __VERIFIER_nondet_int₁₁₁: int, a₁₃: int ::
                                a₁₃ < 100000
                                && x₁₄ == a₁₃
                                && 0 <= a₁₃
                                && a₁₃ < a₅₇
                                && a1₅₅[x₁₄] == __VERIFIER_nondet_int₁₁₁)))
                && (forall x₁₄: int ::
                        (exists a₁₃: int ::
                                x₁₄ == a₁₃
                                && 0 <= a₁₃
                                && a₁₃ < a₅₇)
                        || a1₅₅[x₁₄] == a1[x₁₄])
                && (forall x₁₅: int, a₁₃: int ::
                      (  x₁₅ == a₁₃
                        && 0 <= a₁₃
                        && a₁₃ < a₅₇
                         ==> (exists __VERIFIER_nondet_int₂₁₂: int, a₁₃: int ::
                                a₁₃ < 100000
                                && x₁₅ == a₁₃
                                && 0 <= a₁₃
                                && a₁₃ < a₅₇
                                && a8₅₆[x₁₅] == __VERIFIER_nondet_int₂₁₂)))
                && (forall x₁₅: int ::
                        (exists a₁₃: int ::
                                x₁₅ == a₁₃
                                && 0 <= a₁₃
                                && a₁₃ < a₅₇)
                        || a8₅₆[x₁₅] == a8[x₁₅])
                && (forall a₁₃: int ::
                      (  0 <= a₁₃
                        && a₁₃ < a₅₇
                         ==> a₁₃ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (a₅₇ < 100000
                           ==> 0 <= a₅₇ + 1
                            && a₅₇ + 1 <= 100000
                            && (forall x₁₄: int, a₁₃: int ::
                                  (  x₁₄ == a₁₃
                                    && 0 <= a₁₃
                                    && a₁₃ < a₅₇ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₁₁: int, a₁₃: int ::
                                            a₁₃ < 100000
                                            && x₁₄ == a₁₃
                                            && 0 <= a₁₃
                                            && a₁₃ < a₅₇ + 1
                                            && a1₅₅[a₅₇ := __VERIFIER_nondet_int₁][x₁₄] == __VERIFIER_nondet_int₁₁₁)))
                            && (forall x₁₄: int ::
                                    (exists a₁₃: int ::
                                            x₁₄ == a₁₃
                                            && 0 <= a₁₃
                                            && a₁₃ < a₅₇ + 1)
                                    || a1₅₅[a₅₇ := __VERIFIER_nondet_int₁][x₁₄] == a1[x₁₄])
                            && (forall x₁₅: int, a₁₃: int ::
                                  (  x₁₅ == a₁₃
                                    && 0 <= a₁₃
                                    && a₁₃ < a₅₇ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₁₂: int, a₁₃: int ::
                                            a₁₃ < 100000
                                            && x₁₅ == a₁₃
                                            && 0 <= a₁₃
                                            && a₁₃ < a₅₇ + 1
                                            && a8₅₆[a₅₇ := __VERIFIER_nondet_int₂][x₁₅] == __VERIFIER_nondet_int₂₁₂)))
                            && (forall x₁₅: int ::
                                    (exists a₁₃: int ::
                                            x₁₅ == a₁₃
                                            && 0 <= a₁₃
                                            && a₁₃ < a₅₇ + 1)
                                    || a8₅₆[a₅₇ := __VERIFIER_nondet_int₂][x₁₅] == a8[x₁₅])
                            && (forall a₁₃: int ::
                                  (  0 <= a₁₃
                                    && a₁₃ < a₅₇ + 1
                                     ==> a₁₃ < 100000))))
                  &&   a₅₇ < 100000
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
                                      && a2[x₂₁] == a1₅₅[i₂₀])))
                      && (forall x₂₁: int ::
                              (exists i₂₀: int ::
                                      x₂₁ == i₂₀
                                      && 0 <= i₂₀
                                      && i₂₀ < 0)
                              || a2[x₂₁] == a2[x₂₁])
                      && (forall i₂₀: int ::
                            (  0 <= i₂₀
                              && i₂₀ < 0
                               ==> i₂₀ < 100000))
                      && (forall a2₅₈: [int]int, i₅₉: int ::
                            (  0 <= i₅₉
                              && i₅₉ <= 100000
                              && (forall x₂₁: int, i₂₀: int ::
                                    (  x₂₁ == i₂₀
                                      && 0 <= i₂₀
                                      && i₂₀ < i₅₉
                                       ==> (exists i₂₀: int ::
                                              i₂₀ < 100000
                                              && x₂₁ == i₂₀
                                              && 0 <= i₂₀
                                              && i₂₀ < i₅₉
                                              && a2₅₈[x₂₁] == a1₅₅[i₂₀])))
                              && (forall x₂₁: int ::
                                      (exists i₂₀: int ::
                                              x₂₁ == i₂₀
                                              && 0 <= i₂₀
                                              && i₂₀ < i₅₉)
                                      || a2₅₈[x₂₁] == a2[x₂₁])
                              && (forall i₂₀: int ::
                                    (  0 <= i₂₀
                                      && i₂₀ < i₅₉
                                       ==> i₂₀ < 100000))
                               ==> (i₅₉ < 100000
                                   ==> 0 <= i₅₉ + 1
                                    && i₅₉ + 1 <= 100000
                                    && (forall x₂₁: int, i₂₀: int ::
                                          (  x₂₁ == i₂₀
                                            && 0 <= i₂₀
                                            && i₂₀ < i₅₉ + 1
                                             ==> (exists i₂₀: int ::
                                                    i₂₀ < 100000
                                                    && x₂₁ == i₂₀
                                                    && 0 <= i₂₀
                                                    && i₂₀ < i₅₉ + 1
                                                    && a2₅₈[i₅₉ := a1₅₅[i₅₉]][x₂₁] == a1₅₅[i₂₀])))
                                    && (forall x₂₁: int ::
                                            (exists i₂₀: int ::
                                                    x₂₁ == i₂₀
                                                    && 0 <= i₂₀
                                                    && i₂₀ < i₅₉ + 1)
                                            || a2₅₈[i₅₉ := a1₅₅[i₅₉]][x₂₁] == a2[x₂₁])
                                    && (forall i₂₀: int ::
                                          (  0 <= i₂₀
                                            && i₂₀ < i₅₉ + 1
                                             ==> i₂₀ < 100000)))
                                &&   i₅₉ < 100000
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
                                                    && a3[x₂₅] == a2₅₈[i₂₄])))
                                    && (forall x₂₅: int ::
                                            (exists i₂₄: int ::
                                                    x₂₅ == i₂₄
                                                    && 0 <= i₂₄
                                                    && i₂₄ < 0)
                                            || a3[x₂₅] == a3[x₂₅])
                                    && (forall i₂₄: int ::
                                          (  0 <= i₂₄
                                            && i₂₄ < 0
                                             ==> i₂₄ < 100000))
                                    && (forall a3₆₀: [int]int, i₆₁: int ::
                                          (  0 <= i₆₁
                                            && i₆₁ <= 100000
                                            && (forall x₂₅: int, i₂₄: int ::
                                                  (  x₂₅ == i₂₄
                                                    && 0 <= i₂₄
                                                    && i₂₄ < i₆₁
                                                     ==> (exists i₂₄: int ::
                                                            i₂₄ < 100000
                                                            && x₂₅ == i₂₄
                                                            && 0 <= i₂₄
                                                            && i₂₄ < i₆₁
                                                            && a3₆₀[x₂₅] == a2₅₈[i₂₄])))
                                            && (forall x₂₅: int ::
                                                    (exists i₂₄: int ::
                                                            x₂₅ == i₂₄
                                                            && 0 <= i₂₄
                                                            && i₂₄ < i₆₁)
                                                    || a3₆₀[x₂₅] == a3[x₂₅])
                                            && (forall i₂₄: int ::
                                                  (  0 <= i₂₄
                                                    && i₂₄ < i₆₁
                                                     ==> i₂₄ < 100000))
                                             ==> (i₆₁ < 100000
                                                 ==> 0 <= i₆₁ + 1
                                                  && i₆₁ + 1 <= 100000
                                                  && (forall x₂₅: int, i₂₄: int ::
                                                        (  x₂₅ == i₂₄
                                                          && 0 <= i₂₄
                                                          && i₂₄ < i₆₁ + 1
                                                           ==> (exists i₂₄: int ::
                                                                  i₂₄ < 100000
                                                                  && x₂₅ == i₂₄
                                                                  && 0 <= i₂₄
                                                                  && i₂₄ < i₆₁ + 1
                                                                  && a3₆₀[i₆₁ := a2₅₈[i₆₁]][x₂₅] == a2₅₈[i₂₄])))
                                                  && (forall x₂₅: int ::
                                                          (exists i₂₄: int ::
                                                                  x₂₅ == i₂₄
                                                                  && 0 <= i₂₄
                                                                  && i₂₄ < i₆₁ + 1)
                                                          || a3₆₀[i₆₁ := a2₅₈[i₆₁]][x₂₅] == a3[x₂₅])
                                                  && (forall i₂₄: int ::
                                                        (  0 <= i₂₄
                                                          && i₂₄ < i₆₁ + 1
                                                           ==> i₂₄ < 100000)))
                                              &&   i₆₁ < 100000
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
                                                                  && a4[x₂₉] == a3₆₀[i₂₈])))
                                                  && (forall x₂₉: int ::
                                                          (exists i₂₈: int ::
                                                                  x₂₉ == i₂₈
                                                                  && 0 <= i₂₈
                                                                  && i₂₈ < 0)
                                                          || a4[x₂₉] == a4[x₂₉])
                                                  && (forall i₂₈: int ::
                                                        (  0 <= i₂₈
                                                          && i₂₈ < 0
                                                           ==> i₂₈ < 100000))
                                                  && (forall a4₆₂: [int]int, i₆₃: int ::
                                                        (  0 <= i₆₃
                                                          && i₆₃ <= 100000
                                                          && (forall x₂₉: int, i₂₈: int ::
                                                                (  x₂₉ == i₂₈
                                                                  && 0 <= i₂₈
                                                                  && i₂₈ < i₆₃
                                                                   ==> (exists i₂₈: int ::
                                                                          i₂₈ < 100000
                                                                          && x₂₉ == i₂₈
                                                                          && 0 <= i₂₈
                                                                          && i₂₈ < i₆₃
                                                                          && a4₆₂[x₂₉] == a3₆₀[i₂₈])))
                                                          && (forall x₂₉: int ::
                                                                  (exists i₂₈: int ::
                                                                          x₂₉ == i₂₈
                                                                          && 0 <= i₂₈
                                                                          && i₂₈ < i₆₃)
                                                                  || a4₆₂[x₂₉] == a4[x₂₉])
                                                          && (forall i₂₈: int ::
                                                                (  0 <= i₂₈
                                                                  && i₂₈ < i₆₃
                                                                   ==> i₂₈ < 100000))
                                                           ==> (i₆₃ < 100000
                                                               ==> 0 <= i₆₃ + 1
                                                                && i₆₃ + 1 <= 100000
                                                                && (forall x₂₉: int, i₂₈: int ::
                                                                      (  x₂₉ == i₂₈
                                                                        && 0 <= i₂₈
                                                                        && i₂₈ < i₆₃ + 1
                                                                         ==> (exists i₂₈: int ::
                                                                                i₂₈ < 100000
                                                                                && x₂₉ == i₂₈
                                                                                && 0 <= i₂₈
                                                                                && i₂₈ < i₆₃ + 1
                                                                                && a4₆₂[i₆₃ := a3₆₀[i₆₃]][x₂₉] == a3₆₀[i₂₈])))
                                                                && (forall x₂₉: int ::
                                                                        (exists i₂₈: int ::
                                                                                x₂₉ == i₂₈
                                                                                && 0 <= i₂₈
                                                                                && i₂₈ < i₆₃ + 1)
                                                                        || a4₆₂[i₆₃ := a3₆₀[i₆₃]][x₂₉] == a4[x₂₉])
                                                                && (forall i₂₈: int ::
                                                                      (  0 <= i₂₈
                                                                        && i₂₈ < i₆₃ + 1
                                                                         ==> i₂₈ < 100000)))
                                                            &&   i₆₃ < 100000
                                                              ||   0 <= 0
                                                                && 0 <= 100000
                                                                && (forall x₃₃: int, i₃₂: int ::
                                                                      (  x₃₃ == i₃₂
                                                                        && 0 <= i₃₂
                                                                        && i₃₂ < 0
                                                                         ==> (exists i₃₂: int ::
                                                                                i₃₂ < 100000
                                                                                && x₃₃ == i₃₂
                                                                                && 0 <= i₃₂
                                                                                && i₃₂ < 0
                                                                                && a5[x₃₃] == a4₆₂[i₃₂])))
                                                                && (forall x₃₃: int ::
                                                                        (exists i₃₂: int ::
                                                                                x₃₃ == i₃₂
                                                                                && 0 <= i₃₂
                                                                                && i₃₂ < 0)
                                                                        || a5[x₃₃] == a5[x₃₃])
                                                                && (forall i₃₂: int ::
                                                                      (  0 <= i₃₂
                                                                        && i₃₂ < 0
                                                                         ==> i₃₂ < 100000))
                                                                && (forall a5₆₄: [int]int, i₆₅: int ::
                                                                      (  0 <= i₆₅
                                                                        && i₆₅ <= 100000
                                                                        && (forall x₃₃: int, i₃₂: int ::
                                                                              (  x₃₃ == i₃₂
                                                                                && 0 <= i₃₂
                                                                                && i₃₂ < i₆₅
                                                                                 ==> (exists i₃₂: int ::
                                                                                        i₃₂ < 100000
                                                                                        && x₃₃ == i₃₂
                                                                                        && 0 <= i₃₂
                                                                                        && i₃₂ < i₆₅
                                                                                        && a5₆₄[x₃₃] == a4₆₂[i₃₂])))
                                                                        && (forall x₃₃: int ::
                                                                                (exists i₃₂: int ::
                                                                                        x₃₃ == i₃₂
                                                                                        && 0 <= i₃₂
                                                                                        && i₃₂ < i₆₅)
                                                                                || a5₆₄[x₃₃] == a5[x₃₃])
                                                                        && (forall i₃₂: int ::
                                                                              (  0 <= i₃₂
                                                                                && i₃₂ < i₆₅
                                                                                 ==> i₃₂ < 100000))
                                                                         ==> (i₆₅ < 100000
                                                                             ==> 0 <= i₆₅ + 1
                                                                              && i₆₅ + 1 <= 100000
                                                                              && (forall x₃₃: int, i₃₂: int ::
                                                                                    (  x₃₃ == i₃₂
                                                                                      && 0 <= i₃₂
                                                                                      && i₃₂ < i₆₅ + 1
                                                                                       ==> (exists i₃₂: int ::
                                                                                              i₃₂ < 100000
                                                                                              && x₃₃ == i₃₂
                                                                                              && 0 <= i₃₂
                                                                                              && i₃₂ < i₆₅ + 1
                                                                                              && a5₆₄[i₆₅ := a4₆₂[i₆₅]][x₃₃] == a4₆₂[i₃₂])))
                                                                              && (forall x₃₃: int ::
                                                                                      (exists i₃₂: int ::
                                                                                              x₃₃ == i₃₂
                                                                                              && 0 <= i₃₂
                                                                                              && i₃₂ < i₆₅ + 1)
                                                                                      || a5₆₄[i₆₅ := a4₆₂[i₆₅]][x₃₃] == a5[x₃₃])
                                                                              && (forall i₃₂: int ::
                                                                                    (  0 <= i₃₂
                                                                                      && i₃₂ < i₆₅ + 1
                                                                                       ==> i₃₂ < 100000)))
                                                                          &&   i₆₅ < 100000
                                                                            ||   0 <= 0
                                                                              && 0 <= 100000
                                                                              && (forall x₃₇: int, i₃₆: int ::
                                                                                    (  x₃₇ == i₃₆
                                                                                      && 0 <= i₃₆
                                                                                      && i₃₆ < 0
                                                                                       ==> (exists i₃₆: int ::
                                                                                              i₃₆ < 100000
                                                                                              && x₃₇ == i₃₆
                                                                                              && 0 <= i₃₆
                                                                                              && i₃₆ < 0
                                                                                              && a6[x₃₇] == a5₆₄[i₃₆])))
                                                                              && (forall x₃₇: int ::
                                                                                      (exists i₃₆: int ::
                                                                                              x₃₇ == i₃₆
                                                                                              && 0 <= i₃₆
                                                                                              && i₃₆ < 0)
                                                                                      || a6[x₃₇] == a6[x₃₇])
                                                                              && (forall i₃₆: int ::
                                                                                    (  0 <= i₃₆
                                                                                      && i₃₆ < 0
                                                                                       ==> i₃₆ < 100000))
                                                                              && (forall a6₆₆: [int]int, i₆₇: int ::
                                                                                    (  0 <= i₆₇
                                                                                      && i₆₇ <= 100000
                                                                                      && (forall x₃₇: int, i₃₆: int ::
                                                                                            (  x₃₇ == i₃₆
                                                                                              && 0 <= i₃₆
                                                                                              && i₃₆ < i₆₇
                                                                                               ==> (exists i₃₆: int ::
                                                                                                      i₃₆ < 100000
                                                                                                      && x₃₇ == i₃₆
                                                                                                      && 0 <= i₃₆
                                                                                                      && i₃₆ < i₆₇
                                                                                                      && a6₆₆[x₃₇] == a5₆₄[i₃₆])))
                                                                                      && (forall x₃₇: int ::
                                                                                              (exists i₃₆: int ::
                                                                                                      x₃₇ == i₃₆
                                                                                                      && 0 <= i₃₆
                                                                                                      && i₃₆ < i₆₇)
                                                                                              || a6₆₆[x₃₇] == a6[x₃₇])
                                                                                      && (forall i₃₆: int ::
                                                                                            (  0 <= i₃₆
                                                                                              && i₃₆ < i₆₇
                                                                                               ==> i₃₆ < 100000))
                                                                                       ==> (i₆₇ < 100000
                                                                                           ==> 0 <= i₆₇ + 1
                                                                                            && i₆₇ + 1 <= 100000
                                                                                            && (forall x₃₇: int, i₃₆: int ::
                                                                                                  (  x₃₇ == i₃₆
                                                                                                    && 0 <= i₃₆
                                                                                                    && i₃₆ < i₆₇ + 1
                                                                                                     ==> (exists i₃₆: int ::
                                                                                                            i₃₆ < 100000
                                                                                                            && x₃₇ == i₃₆
                                                                                                            && 0 <= i₃₆
                                                                                                            && i₃₆ < i₆₇ + 1
                                                                                                            && a6₆₆[i₆₇ := a5₆₄[i₆₇]][x₃₇] == a5₆₄[i₃₆])))
                                                                                            && (forall x₃₇: int ::
                                                                                                    (exists i₃₆: int ::
                                                                                                            x₃₇ == i₃₆
                                                                                                            && 0 <= i₃₆
                                                                                                            && i₃₆ < i₆₇ + 1)
                                                                                                    || a6₆₆[i₆₇ := a5₆₄[i₆₇]][x₃₇] == a6[x₃₇])
                                                                                            && (forall i₃₆: int ::
                                                                                                  (  0 <= i₃₆
                                                                                                    && i₃₆ < i₆₇ + 1
                                                                                                     ==> i₃₆ < 100000)))
                                                                                        &&   i₆₇ < 100000
                                                                                          ||   0 <= 0
                                                                                            && 0 <= 100000
                                                                                            && (forall x₄₁: int, i₄₀: int ::
                                                                                                  (  x₄₁ == i₄₀
                                                                                                    && 0 <= i₄₀
                                                                                                    && i₄₀ < 0
                                                                                                     ==> (exists i₄₀: int ::
                                                                                                            i₄₀ < 100000
                                                                                                            && x₄₁ == i₄₀
                                                                                                            && 0 <= i₄₀
                                                                                                            && i₄₀ < 0
                                                                                                            && a7[x₄₁] == a6₆₆[i₄₀])))
                                                                                            && (forall x₄₁: int ::
                                                                                                    (exists i₄₀: int ::
                                                                                                            x₄₁ == i₄₀
                                                                                                            && 0 <= i₄₀
                                                                                                            && i₄₀ < 0)
                                                                                                    || a7[x₄₁] == a7[x₄₁])
                                                                                            && (forall i₄₀: int ::
                                                                                                  (  0 <= i₄₀
                                                                                                    && i₄₀ < 0
                                                                                                     ==> i₄₀ < 100000))
                                                                                            && (forall a7₆₈: [int]int, i₆₉: int ::
                                                                                                  (  0 <= i₆₉
                                                                                                    && i₆₉ <= 100000
                                                                                                    && (forall x₄₁: int, i₄₀: int ::
                                                                                                          (  x₄₁ == i₄₀
                                                                                                            && 0 <= i₄₀
                                                                                                            && i₄₀ < i₆₉
                                                                                                             ==> (exists i₄₀: int ::
                                                                                                                    i₄₀ < 100000
                                                                                                                    && x₄₁ == i₄₀
                                                                                                                    && 0 <= i₄₀
                                                                                                                    && i₄₀ < i₆₉
                                                                                                                    && a7₆₈[x₄₁] == a6₆₆[i₄₀])))
                                                                                                    && (forall x₄₁: int ::
                                                                                                            (exists i₄₀: int ::
                                                                                                                    x₄₁ == i₄₀
                                                                                                                    && 0 <= i₄₀
                                                                                                                    && i₄₀ < i₆₉)
                                                                                                            || a7₆₈[x₄₁] == a7[x₄₁])
                                                                                                    && (forall i₄₀: int ::
                                                                                                          (  0 <= i₄₀
                                                                                                            && i₄₀ < i₆₉
                                                                                                             ==> i₄₀ < 100000))
                                                                                                     ==> (i₆₉ < 100000
                                                                                                         ==> 0 <= i₆₉ + 1
                                                                                                          && i₆₉ + 1 <= 100000
                                                                                                          && (forall x₄₁: int, i₄₀: int ::
                                                                                                                (  x₄₁ == i₄₀
                                                                                                                  && 0 <= i₄₀
                                                                                                                  && i₄₀ < i₆₉ + 1
                                                                                                                   ==> (exists i₄₀: int ::
                                                                                                                          i₄₀ < 100000
                                                                                                                          && x₄₁ == i₄₀
                                                                                                                          && 0 <= i₄₀
                                                                                                                          && i₄₀ < i₆₉ + 1
                                                                                                                          && a7₆₈[i₆₉ := a6₆₆[i₆₉]][x₄₁] == a6₆₆[i₄₀])))
                                                                                                          && (forall x₄₁: int ::
                                                                                                                  (exists i₄₀: int ::
                                                                                                                          x₄₁ == i₄₀
                                                                                                                          && 0 <= i₄₀
                                                                                                                          && i₄₀ < i₆₉ + 1)
                                                                                                                  || a7₆₈[i₆₉ := a6₆₆[i₆₉]][x₄₁] == a7[x₄₁])
                                                                                                          && (forall i₄₀: int ::
                                                                                                                (  0 <= i₄₀
                                                                                                                  && i₄₀ < i₆₉ + 1
                                                                                                                   ==> i₄₀ < 100000)))
                                                                                                      &&   i₆₉ < 100000
                                                                                                        ||   0 <= 0
                                                                                                          && 0 <= 100000
                                                                                                          && (forall x₄₅: int, i₄₄: int ::
                                                                                                                (  x₄₅ == i₄₄
                                                                                                                  && 0 <= i₄₄
                                                                                                                  && i₄₄ < 0
                                                                                                                   ==> (exists i₄₄: int ::
                                                                                                                          i₄₄ < 100000
                                                                                                                          && x₄₅ == i₄₄
                                                                                                                          && 0 <= i₄₄
                                                                                                                          && i₄₄ < 0
                                                                                                                          && a9[x₄₅] == a7₆₈[i₄₄])))
                                                                                                          && (forall x₄₅: int ::
                                                                                                                  (exists i₄₄: int ::
                                                                                                                          x₄₅ == i₄₄
                                                                                                                          && 0 <= i₄₄
                                                                                                                          && i₄₄ < 0)
                                                                                                                  || a9[x₄₅] == a9[x₄₅])
                                                                                                          && (forall i₄₄: int ::
                                                                                                                (  0 <= i₄₄
                                                                                                                  && i₄₄ < 0
                                                                                                                   ==> i₄₄ < 100000))
                                                                                                          && (forall a9₇₀: [int]int, i₇₁: int ::
                                                                                                                (  0 <= i₇₁
                                                                                                                  && i₇₁ <= 100000
                                                                                                                  && (forall x₄₅: int, i₄₄: int ::
                                                                                                                        (  x₄₅ == i₄₄
                                                                                                                          && 0 <= i₄₄
                                                                                                                          && i₄₄ < i₇₁
                                                                                                                           ==> (exists i₄₄: int ::
                                                                                                                                  i₄₄ < 100000
                                                                                                                                  && x₄₅ == i₄₄
                                                                                                                                  && 0 <= i₄₄
                                                                                                                                  && i₄₄ < i₇₁
                                                                                                                                  && a9₇₀[x₄₅] == a7₆₈[i₄₄])))
                                                                                                                  && (forall x₄₅: int ::
                                                                                                                          (exists i₄₄: int ::
                                                                                                                                  x₄₅ == i₄₄
                                                                                                                                  && 0 <= i₄₄
                                                                                                                                  && i₄₄ < i₇₁)
                                                                                                                          || a9₇₀[x₄₅] == a9[x₄₅])
                                                                                                                  && (forall i₄₄: int ::
                                                                                                                        (  0 <= i₄₄
                                                                                                                          && i₄₄ < i₇₁
                                                                                                                           ==> i₄₄ < 100000))
                                                                                                                   ==> (i₇₁ < 100000
                                                                                                                       ==> 0 <= i₇₁ + 1
                                                                                                                        && i₇₁ + 1 <= 100000
                                                                                                                        && (forall x₄₅: int, i₄₄: int ::
                                                                                                                              (  x₄₅ == i₄₄
                                                                                                                                && 0 <= i₄₄
                                                                                                                                && i₄₄ < i₇₁ + 1
                                                                                                                                 ==> (exists i₄₄: int ::
                                                                                                                                        i₄₄ < 100000
                                                                                                                                        && x₄₅ == i₄₄
                                                                                                                                        && 0 <= i₄₄
                                                                                                                                        && i₄₄ < i₇₁ + 1
                                                                                                                                        && a9₇₀[i₇₁ := a7₆₈[i₇₁]][x₄₅] == a7₆₈[i₄₄])))
                                                                                                                        && (forall x₄₅: int ::
                                                                                                                                (exists i₄₄: int ::
                                                                                                                                        x₄₅ == i₄₄
                                                                                                                                        && 0 <= i₄₄
                                                                                                                                        && i₄₄ < i₇₁ + 1)
                                                                                                                                || a9₇₀[i₇₁ := a7₆₈[i₇₁]][x₄₅] == a9[x₄₅])
                                                                                                                        && (forall i₄₄: int ::
                                                                                                                              (  0 <= i₄₄
                                                                                                                                && i₄₄ < i₇₁ + 1
                                                                                                                                 ==> i₄₄ < 100000)))
                                                                                                                    &&   i₇₁ < 100000
                                                                                                                      ||   0 <= 0
                                                                                                                        && 0 <= 100000
                                                                                                                        && (forall x₄₉: int, i₄₈: int ::
                                                                                                                              (  x₄₉ == i₄₈
                                                                                                                                && 0 <= i₄₈
                                                                                                                                && i₄₈ < 0
                                                                                                                                 ==> (exists i₄₈: int ::
                                                                                                                                        i₄₈ < 100000
                                                                                                                                        && x₄₉ == i₄₈
                                                                                                                                        && 0 <= i₄₈
                                                                                                                                        && i₄₈ < 0
                                                                                                                                        && a9₇₀[x₄₉] == a8₅₆[i₄₈])))
                                                                                                                        && (forall x₄₉: int ::
                                                                                                                                (exists i₄₈: int ::
                                                                                                                                        x₄₉ == i₄₈
                                                                                                                                        && 0 <= i₄₈
                                                                                                                                        && i₄₈ < 0)
                                                                                                                                || a9₇₀[x₄₉] == a9₇₀[x₄₉])
                                                                                                                        && (forall i₄₈: int ::
                                                                                                                              (  0 <= i₄₈
                                                                                                                                && i₄₈ < 0
                                                                                                                                 ==> i₄₈ < 100000))
                                                                                                                        && (forall a9₇₂: [int]int, i₇₃: int ::
                                                                                                                              (  0 <= i₇₃
                                                                                                                                && i₇₃ <= 100000
                                                                                                                                && (forall x₄₉: int, i₄₈: int ::
                                                                                                                                      (  x₄₉ == i₄₈
                                                                                                                                        && 0 <= i₄₈
                                                                                                                                        && i₄₈ < i₇₃
                                                                                                                                         ==> (exists i₄₈: int ::
                                                                                                                                                i₄₈ < 100000
                                                                                                                                                && x₄₉ == i₄₈
                                                                                                                                                && 0 <= i₄₈
                                                                                                                                                && i₄₈ < i₇₃
                                                                                                                                                && a9₇₂[x₄₉] == a8₅₆[i₄₈])))
                                                                                                                                && (forall x₄₉: int ::
                                                                                                                                        (exists i₄₈: int ::
                                                                                                                                                x₄₉ == i₄₈
                                                                                                                                                && 0 <= i₄₈
                                                                                                                                                && i₄₈ < i₇₃)
                                                                                                                                        || a9₇₂[x₄₉] == a9₇₀[x₄₉])
                                                                                                                                && (forall i₄₈: int ::
                                                                                                                                      (  0 <= i₄₈
                                                                                                                                        && i₄₈ < i₇₃
                                                                                                                                         ==> i₄₈ < 100000))
                                                                                                                                 ==> (i₇₃ < 100000
                                                                                                                                     ==> 0 <= i₇₃ + 1
                                                                                                                                      && i₇₃ + 1 <= 100000
                                                                                                                                      && (forall x₄₉: int, i₄₈: int ::
                                                                                                                                            (  x₄₉ == i₄₈
                                                                                                                                              && 0 <= i₄₈
                                                                                                                                              && i₄₈ < i₇₃ + 1
                                                                                                                                               ==> (exists i₄₈: int ::
                                                                                                                                                      i₄₈ < 100000
                                                                                                                                                      && x₄₉ == i₄₈
                                                                                                                                                      && 0 <= i₄₈
                                                                                                                                                      && i₄₈ < i₇₃ + 1
                                                                                                                                                      && a9₇₂[i₇₃ := a8₅₆[i₇₃]][x₄₉] == a8₅₆[i₄₈])))
                                                                                                                                      && (forall x₄₉: int ::
                                                                                                                                              (exists i₄₈: int ::
                                                                                                                                                      x₄₉ == i₄₈
                                                                                                                                                      && 0 <= i₄₈
                                                                                                                                                      && i₄₈ < i₇₃ + 1)
                                                                                                                                              || a9₇₂[i₇₃ := a8₅₆[i₇₃]][x₄₉] == a9₇₀[x₄₉])
                                                                                                                                      && (forall i₄₈: int ::
                                                                                                                                            (  0 <= i₄₈
                                                                                                                                              && i₄₈ < i₇₃ + 1
                                                                                                                                               ==> i₄₈ < 100000)))
                                                                                                                                  &&   i₇₃ < 100000
                                                                                                                                    ||   0 <= 0
                                                                                                                                      && 0 <= 100000
                                                                                                                                      && (forall x₅₃: int ::
                                                                                                                                            (  0 <= x₅₃
                                                                                                                                              && x₅₃ < 0
                                                                                                                                               ==> x₅₃ < 100000))
                                                                                                                                      && (forall x₇₄: int ::
                                                                                                                                            (  0 <= x₇₄
                                                                                                                                              && x₇₄ <= 100000
                                                                                                                                              && (forall x₅₃: int ::
                                                                                                                                                    (  0 <= x₅₃
                                                                                                                                                      && x₅₃ < x₇₄
                                                                                                                                                       ==> x₅₃ < 100000))
                                                                                                                                               ==> (x₇₄ < 100000
                                                                                                                                                 ==> a1₅₅[x₇₄] == a9₇₂[x₇₄]
                                                                                                                                                  && 0 <= x₇₄ + 1
                                                                                                                                                  && x₇₄ + 1 <= 100000
                                                                                                                                                  && (forall x₅₃: int ::
                                                                                                                                                        (  0 <= x₅₃
                                                                                                                                                          && x₅₃ < x₇₄ + 1
                                                                                                                                                           ==> x₅₃ < 100000))))))))))))))))))))))));


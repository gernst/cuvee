data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int, a3: [int]int, a4: [int]int, a5: [int]int, a6: [int]int, a7: [int]int, a8: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₁₃: int, a₁₂: int ::
              (  x₁₃ == a₁₂
                && 0 <= a₁₂
                && a₁₂ < 0
                 ==> (exists __VERIFIER_nondet_int₁₁₀: int, a₁₂: int ::
                        a₁₂ < 100000
                        && x₁₃ == a₁₂
                        && 0 <= a₁₂
                        && a₁₂ < 0
                        && a1[x₁₃] == __VERIFIER_nondet_int₁₁₀)))
        && (forall x₁₃: int ::
                (exists a₁₂: int ::
                        x₁₃ == a₁₂
                        && 0 <= a₁₂
                        && a₁₂ < 0)
                || a1[x₁₃] == a1[x₁₃])
        && (forall x₁₄: int, a₁₂: int ::
              (  x₁₄ == a₁₂
                && 0 <= a₁₂
                && a₁₂ < 0
                 ==> (exists __VERIFIER_nondet_int₂₁₁: int, a₁₂: int ::
                        a₁₂ < 100000
                        && x₁₄ == a₁₂
                        && 0 <= a₁₂
                        && a₁₂ < 0
                        && a7[x₁₄] == __VERIFIER_nondet_int₂₁₁)))
        && (forall x₁₄: int ::
                (exists a₁₂: int ::
                        x₁₄ == a₁₂
                        && 0 <= a₁₂
                        && a₁₂ < 0)
                || a7[x₁₄] == a7[x₁₄])
        && (forall a₁₂: int ::
              (  0 <= a₁₂
                && a₁₂ < 0
                 ==> a₁₂ < 100000))
        && (forall a1₅₀: [int]int, a7₅₁: [int]int, a₅₂: int ::
              (  0 <= a₅₂
                && a₅₂ <= 100000
                && (forall x₁₃: int, a₁₂: int ::
                      (  x₁₃ == a₁₂
                        && 0 <= a₁₂
                        && a₁₂ < a₅₂
                         ==> (exists __VERIFIER_nondet_int₁₁₀: int, a₁₂: int ::
                                a₁₂ < 100000
                                && x₁₃ == a₁₂
                                && 0 <= a₁₂
                                && a₁₂ < a₅₂
                                && a1₅₀[x₁₃] == __VERIFIER_nondet_int₁₁₀)))
                && (forall x₁₃: int ::
                        (exists a₁₂: int ::
                                x₁₃ == a₁₂
                                && 0 <= a₁₂
                                && a₁₂ < a₅₂)
                        || a1₅₀[x₁₃] == a1[x₁₃])
                && (forall x₁₄: int, a₁₂: int ::
                      (  x₁₄ == a₁₂
                        && 0 <= a₁₂
                        && a₁₂ < a₅₂
                         ==> (exists __VERIFIER_nondet_int₂₁₁: int, a₁₂: int ::
                                a₁₂ < 100000
                                && x₁₄ == a₁₂
                                && 0 <= a₁₂
                                && a₁₂ < a₅₂
                                && a7₅₁[x₁₄] == __VERIFIER_nondet_int₂₁₁)))
                && (forall x₁₄: int ::
                        (exists a₁₂: int ::
                                x₁₄ == a₁₂
                                && 0 <= a₁₂
                                && a₁₂ < a₅₂)
                        || a7₅₁[x₁₄] == a7[x₁₄])
                && (forall a₁₂: int ::
                      (  0 <= a₁₂
                        && a₁₂ < a₅₂
                         ==> a₁₂ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (a₅₂ < 100000
                           ==> 0 <= a₅₂ + 1
                            && a₅₂ + 1 <= 100000
                            && (forall x₁₃: int, a₁₂: int ::
                                  (  x₁₃ == a₁₂
                                    && 0 <= a₁₂
                                    && a₁₂ < a₅₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₁₀: int, a₁₂: int ::
                                            a₁₂ < 100000
                                            && x₁₃ == a₁₂
                                            && 0 <= a₁₂
                                            && a₁₂ < a₅₂ + 1
                                            && a1₅₀[a₅₂ := __VERIFIER_nondet_int₁][x₁₃] == __VERIFIER_nondet_int₁₁₀)))
                            && (forall x₁₃: int ::
                                    (exists a₁₂: int ::
                                            x₁₃ == a₁₂
                                            && 0 <= a₁₂
                                            && a₁₂ < a₅₂ + 1)
                                    || a1₅₀[a₅₂ := __VERIFIER_nondet_int₁][x₁₃] == a1[x₁₃])
                            && (forall x₁₄: int, a₁₂: int ::
                                  (  x₁₄ == a₁₂
                                    && 0 <= a₁₂
                                    && a₁₂ < a₅₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₁₁: int, a₁₂: int ::
                                            a₁₂ < 100000
                                            && x₁₄ == a₁₂
                                            && 0 <= a₁₂
                                            && a₁₂ < a₅₂ + 1
                                            && a7₅₁[a₅₂ := __VERIFIER_nondet_int₂][x₁₄] == __VERIFIER_nondet_int₂₁₁)))
                            && (forall x₁₄: int ::
                                    (exists a₁₂: int ::
                                            x₁₄ == a₁₂
                                            && 0 <= a₁₂
                                            && a₁₂ < a₅₂ + 1)
                                    || a7₅₁[a₅₂ := __VERIFIER_nondet_int₂][x₁₄] == a7[x₁₄])
                            && (forall a₁₂: int ::
                                  (  0 <= a₁₂
                                    && a₁₂ < a₅₂ + 1
                                     ==> a₁₂ < 100000))))
                  &&   a₅₂ < 100000
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
                                      && a2[x₂₀] == a1₅₀[i₁₉])))
                      && (forall x₂₀: int ::
                              (exists i₁₉: int ::
                                      x₂₀ == i₁₉
                                      && 0 <= i₁₉
                                      && i₁₉ < 0)
                              || a2[x₂₀] == a2[x₂₀])
                      && (forall i₁₉: int ::
                            (  0 <= i₁₉
                              && i₁₉ < 0
                               ==> i₁₉ < 100000))
                      && (forall a2₅₃: [int]int, i₅₄: int ::
                            (  0 <= i₅₄
                              && i₅₄ <= 100000
                              && (forall x₂₀: int, i₁₉: int ::
                                    (  x₂₀ == i₁₉
                                      && 0 <= i₁₉
                                      && i₁₉ < i₅₄
                                       ==> (exists i₁₉: int ::
                                              i₁₉ < 100000
                                              && x₂₀ == i₁₉
                                              && 0 <= i₁₉
                                              && i₁₉ < i₅₄
                                              && a2₅₃[x₂₀] == a1₅₀[i₁₉])))
                              && (forall x₂₀: int ::
                                      (exists i₁₉: int ::
                                              x₂₀ == i₁₉
                                              && 0 <= i₁₉
                                              && i₁₉ < i₅₄)
                                      || a2₅₃[x₂₀] == a2[x₂₀])
                              && (forall i₁₉: int ::
                                    (  0 <= i₁₉
                                      && i₁₉ < i₅₄
                                       ==> i₁₉ < 100000))
                               ==> (i₅₄ < 100000
                                   ==> 0 <= i₅₄ + 1
                                    && i₅₄ + 1 <= 100000
                                    && (forall x₂₀: int, i₁₉: int ::
                                          (  x₂₀ == i₁₉
                                            && 0 <= i₁₉
                                            && i₁₉ < i₅₄ + 1
                                             ==> (exists i₁₉: int ::
                                                    i₁₉ < 100000
                                                    && x₂₀ == i₁₉
                                                    && 0 <= i₁₉
                                                    && i₁₉ < i₅₄ + 1
                                                    && a2₅₃[i₅₄ := a1₅₀[i₅₄]][x₂₀] == a1₅₀[i₁₉])))
                                    && (forall x₂₀: int ::
                                            (exists i₁₉: int ::
                                                    x₂₀ == i₁₉
                                                    && 0 <= i₁₉
                                                    && i₁₉ < i₅₄ + 1)
                                            || a2₅₃[i₅₄ := a1₅₀[i₅₄]][x₂₀] == a2[x₂₀])
                                    && (forall i₁₉: int ::
                                          (  0 <= i₁₉
                                            && i₁₉ < i₅₄ + 1
                                             ==> i₁₉ < 100000)))
                                &&   i₅₄ < 100000
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
                                                    && a3[x₂₄] == a2₅₃[i₂₃])))
                                    && (forall x₂₄: int ::
                                            (exists i₂₃: int ::
                                                    x₂₄ == i₂₃
                                                    && 0 <= i₂₃
                                                    && i₂₃ < 0)
                                            || a3[x₂₄] == a3[x₂₄])
                                    && (forall i₂₃: int ::
                                          (  0 <= i₂₃
                                            && i₂₃ < 0
                                             ==> i₂₃ < 100000))
                                    && (forall a3₅₅: [int]int, i₅₆: int ::
                                          (  0 <= i₅₆
                                            && i₅₆ <= 100000
                                            && (forall x₂₄: int, i₂₃: int ::
                                                  (  x₂₄ == i₂₃
                                                    && 0 <= i₂₃
                                                    && i₂₃ < i₅₆
                                                     ==> (exists i₂₃: int ::
                                                            i₂₃ < 100000
                                                            && x₂₄ == i₂₃
                                                            && 0 <= i₂₃
                                                            && i₂₃ < i₅₆
                                                            && a3₅₅[x₂₄] == a2₅₃[i₂₃])))
                                            && (forall x₂₄: int ::
                                                    (exists i₂₃: int ::
                                                            x₂₄ == i₂₃
                                                            && 0 <= i₂₃
                                                            && i₂₃ < i₅₆)
                                                    || a3₅₅[x₂₄] == a3[x₂₄])
                                            && (forall i₂₃: int ::
                                                  (  0 <= i₂₃
                                                    && i₂₃ < i₅₆
                                                     ==> i₂₃ < 100000))
                                             ==> (i₅₆ < 100000
                                                 ==> 0 <= i₅₆ + 1
                                                  && i₅₆ + 1 <= 100000
                                                  && (forall x₂₄: int, i₂₃: int ::
                                                        (  x₂₄ == i₂₃
                                                          && 0 <= i₂₃
                                                          && i₂₃ < i₅₆ + 1
                                                           ==> (exists i₂₃: int ::
                                                                  i₂₃ < 100000
                                                                  && x₂₄ == i₂₃
                                                                  && 0 <= i₂₃
                                                                  && i₂₃ < i₅₆ + 1
                                                                  && a3₅₅[i₅₆ := a2₅₃[i₅₆]][x₂₄] == a2₅₃[i₂₃])))
                                                  && (forall x₂₄: int ::
                                                          (exists i₂₃: int ::
                                                                  x₂₄ == i₂₃
                                                                  && 0 <= i₂₃
                                                                  && i₂₃ < i₅₆ + 1)
                                                          || a3₅₅[i₅₆ := a2₅₃[i₅₆]][x₂₄] == a3[x₂₄])
                                                  && (forall i₂₃: int ::
                                                        (  0 <= i₂₃
                                                          && i₂₃ < i₅₆ + 1
                                                           ==> i₂₃ < 100000)))
                                              &&   i₅₆ < 100000
                                                ||   0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₂₈: int, i₂₇: int ::
                                                        (  x₂₈ == i₂₇
                                                          && 0 <= i₂₇
                                                          && i₂₇ < 0
                                                           ==> (exists i₂₇: int ::
                                                                  i₂₇ < 100000
                                                                  && x₂₈ == i₂₇
                                                                  && 0 <= i₂₇
                                                                  && i₂₇ < 0
                                                                  && a4[x₂₈] == a3₅₅[i₂₇])))
                                                  && (forall x₂₈: int ::
                                                          (exists i₂₇: int ::
                                                                  x₂₈ == i₂₇
                                                                  && 0 <= i₂₇
                                                                  && i₂₇ < 0)
                                                          || a4[x₂₈] == a4[x₂₈])
                                                  && (forall i₂₇: int ::
                                                        (  0 <= i₂₇
                                                          && i₂₇ < 0
                                                           ==> i₂₇ < 100000))
                                                  && (forall a4₅₇: [int]int, i₅₈: int ::
                                                        (  0 <= i₅₈
                                                          && i₅₈ <= 100000
                                                          && (forall x₂₈: int, i₂₇: int ::
                                                                (  x₂₈ == i₂₇
                                                                  && 0 <= i₂₇
                                                                  && i₂₇ < i₅₈
                                                                   ==> (exists i₂₇: int ::
                                                                          i₂₇ < 100000
                                                                          && x₂₈ == i₂₇
                                                                          && 0 <= i₂₇
                                                                          && i₂₇ < i₅₈
                                                                          && a4₅₇[x₂₈] == a3₅₅[i₂₇])))
                                                          && (forall x₂₈: int ::
                                                                  (exists i₂₇: int ::
                                                                          x₂₈ == i₂₇
                                                                          && 0 <= i₂₇
                                                                          && i₂₇ < i₅₈)
                                                                  || a4₅₇[x₂₈] == a4[x₂₈])
                                                          && (forall i₂₇: int ::
                                                                (  0 <= i₂₇
                                                                  && i₂₇ < i₅₈
                                                                   ==> i₂₇ < 100000))
                                                           ==> (i₅₈ < 100000
                                                               ==> 0 <= i₅₈ + 1
                                                                && i₅₈ + 1 <= 100000
                                                                && (forall x₂₈: int, i₂₇: int ::
                                                                      (  x₂₈ == i₂₇
                                                                        && 0 <= i₂₇
                                                                        && i₂₇ < i₅₈ + 1
                                                                         ==> (exists i₂₇: int ::
                                                                                i₂₇ < 100000
                                                                                && x₂₈ == i₂₇
                                                                                && 0 <= i₂₇
                                                                                && i₂₇ < i₅₈ + 1
                                                                                && a4₅₇[i₅₈ := a3₅₅[i₅₈]][x₂₈] == a3₅₅[i₂₇])))
                                                                && (forall x₂₈: int ::
                                                                        (exists i₂₇: int ::
                                                                                x₂₈ == i₂₇
                                                                                && 0 <= i₂₇
                                                                                && i₂₇ < i₅₈ + 1)
                                                                        || a4₅₇[i₅₈ := a3₅₅[i₅₈]][x₂₈] == a4[x₂₈])
                                                                && (forall i₂₇: int ::
                                                                      (  0 <= i₂₇
                                                                        && i₂₇ < i₅₈ + 1
                                                                         ==> i₂₇ < 100000)))
                                                            &&   i₅₈ < 100000
                                                              ||   0 <= 0
                                                                && 0 <= 100000
                                                                && (forall x₃₂: int, i₃₁: int ::
                                                                      (  x₃₂ == i₃₁
                                                                        && 0 <= i₃₁
                                                                        && i₃₁ < 0
                                                                         ==> (exists i₃₁: int ::
                                                                                i₃₁ < 100000
                                                                                && x₃₂ == i₃₁
                                                                                && 0 <= i₃₁
                                                                                && i₃₁ < 0
                                                                                && a5[x₃₂] == a4₅₇[i₃₁])))
                                                                && (forall x₃₂: int ::
                                                                        (exists i₃₁: int ::
                                                                                x₃₂ == i₃₁
                                                                                && 0 <= i₃₁
                                                                                && i₃₁ < 0)
                                                                        || a5[x₃₂] == a5[x₃₂])
                                                                && (forall i₃₁: int ::
                                                                      (  0 <= i₃₁
                                                                        && i₃₁ < 0
                                                                         ==> i₃₁ < 100000))
                                                                && (forall a5₅₉: [int]int, i₆₀: int ::
                                                                      (  0 <= i₆₀
                                                                        && i₆₀ <= 100000
                                                                        && (forall x₃₂: int, i₃₁: int ::
                                                                              (  x₃₂ == i₃₁
                                                                                && 0 <= i₃₁
                                                                                && i₃₁ < i₆₀
                                                                                 ==> (exists i₃₁: int ::
                                                                                        i₃₁ < 100000
                                                                                        && x₃₂ == i₃₁
                                                                                        && 0 <= i₃₁
                                                                                        && i₃₁ < i₆₀
                                                                                        && a5₅₉[x₃₂] == a4₅₇[i₃₁])))
                                                                        && (forall x₃₂: int ::
                                                                                (exists i₃₁: int ::
                                                                                        x₃₂ == i₃₁
                                                                                        && 0 <= i₃₁
                                                                                        && i₃₁ < i₆₀)
                                                                                || a5₅₉[x₃₂] == a5[x₃₂])
                                                                        && (forall i₃₁: int ::
                                                                              (  0 <= i₃₁
                                                                                && i₃₁ < i₆₀
                                                                                 ==> i₃₁ < 100000))
                                                                         ==> (i₆₀ < 100000
                                                                             ==> 0 <= i₆₀ + 1
                                                                              && i₆₀ + 1 <= 100000
                                                                              && (forall x₃₂: int, i₃₁: int ::
                                                                                    (  x₃₂ == i₃₁
                                                                                      && 0 <= i₃₁
                                                                                      && i₃₁ < i₆₀ + 1
                                                                                       ==> (exists i₃₁: int ::
                                                                                              i₃₁ < 100000
                                                                                              && x₃₂ == i₃₁
                                                                                              && 0 <= i₃₁
                                                                                              && i₃₁ < i₆₀ + 1
                                                                                              && a5₅₉[i₆₀ := a4₅₇[i₆₀]][x₃₂] == a4₅₇[i₃₁])))
                                                                              && (forall x₃₂: int ::
                                                                                      (exists i₃₁: int ::
                                                                                              x₃₂ == i₃₁
                                                                                              && 0 <= i₃₁
                                                                                              && i₃₁ < i₆₀ + 1)
                                                                                      || a5₅₉[i₆₀ := a4₅₇[i₆₀]][x₃₂] == a5[x₃₂])
                                                                              && (forall i₃₁: int ::
                                                                                    (  0 <= i₃₁
                                                                                      && i₃₁ < i₆₀ + 1
                                                                                       ==> i₃₁ < 100000)))
                                                                          &&   i₆₀ < 100000
                                                                            ||   0 <= 0
                                                                              && 0 <= 100000
                                                                              && (forall x₃₆: int, i₃₅: int ::
                                                                                    (  x₃₆ == i₃₅
                                                                                      && 0 <= i₃₅
                                                                                      && i₃₅ < 0
                                                                                       ==> (exists i₃₅: int ::
                                                                                              i₃₅ < 100000
                                                                                              && x₃₆ == i₃₅
                                                                                              && 0 <= i₃₅
                                                                                              && i₃₅ < 0
                                                                                              && a6[x₃₆] == a5₅₉[i₃₅])))
                                                                              && (forall x₃₆: int ::
                                                                                      (exists i₃₅: int ::
                                                                                              x₃₆ == i₃₅
                                                                                              && 0 <= i₃₅
                                                                                              && i₃₅ < 0)
                                                                                      || a6[x₃₆] == a6[x₃₆])
                                                                              && (forall i₃₅: int ::
                                                                                    (  0 <= i₃₅
                                                                                      && i₃₅ < 0
                                                                                       ==> i₃₅ < 100000))
                                                                              && (forall a6₆₁: [int]int, i₆₂: int ::
                                                                                    (  0 <= i₆₂
                                                                                      && i₆₂ <= 100000
                                                                                      && (forall x₃₆: int, i₃₅: int ::
                                                                                            (  x₃₆ == i₃₅
                                                                                              && 0 <= i₃₅
                                                                                              && i₃₅ < i₆₂
                                                                                               ==> (exists i₃₅: int ::
                                                                                                      i₃₅ < 100000
                                                                                                      && x₃₆ == i₃₅
                                                                                                      && 0 <= i₃₅
                                                                                                      && i₃₅ < i₆₂
                                                                                                      && a6₆₁[x₃₆] == a5₅₉[i₃₅])))
                                                                                      && (forall x₃₆: int ::
                                                                                              (exists i₃₅: int ::
                                                                                                      x₃₆ == i₃₅
                                                                                                      && 0 <= i₃₅
                                                                                                      && i₃₅ < i₆₂)
                                                                                              || a6₆₁[x₃₆] == a6[x₃₆])
                                                                                      && (forall i₃₅: int ::
                                                                                            (  0 <= i₃₅
                                                                                              && i₃₅ < i₆₂
                                                                                               ==> i₃₅ < 100000))
                                                                                       ==> (i₆₂ < 100000
                                                                                           ==> 0 <= i₆₂ + 1
                                                                                            && i₆₂ + 1 <= 100000
                                                                                            && (forall x₃₆: int, i₃₅: int ::
                                                                                                  (  x₃₆ == i₃₅
                                                                                                    && 0 <= i₃₅
                                                                                                    && i₃₅ < i₆₂ + 1
                                                                                                     ==> (exists i₃₅: int ::
                                                                                                            i₃₅ < 100000
                                                                                                            && x₃₆ == i₃₅
                                                                                                            && 0 <= i₃₅
                                                                                                            && i₃₅ < i₆₂ + 1
                                                                                                            && a6₆₁[i₆₂ := a5₅₉[i₆₂]][x₃₆] == a5₅₉[i₃₅])))
                                                                                            && (forall x₃₆: int ::
                                                                                                    (exists i₃₅: int ::
                                                                                                            x₃₆ == i₃₅
                                                                                                            && 0 <= i₃₅
                                                                                                            && i₃₅ < i₆₂ + 1)
                                                                                                    || a6₆₁[i₆₂ := a5₅₉[i₆₂]][x₃₆] == a6[x₃₆])
                                                                                            && (forall i₃₅: int ::
                                                                                                  (  0 <= i₃₅
                                                                                                    && i₃₅ < i₆₂ + 1
                                                                                                     ==> i₃₅ < 100000)))
                                                                                        &&   i₆₂ < 100000
                                                                                          ||   0 <= 0
                                                                                            && 0 <= 100000
                                                                                            && (forall x₄₀: int, i₃₉: int ::
                                                                                                  (  x₄₀ == i₃₉
                                                                                                    && 0 <= i₃₉
                                                                                                    && i₃₉ < 0
                                                                                                     ==> (exists i₃₉: int ::
                                                                                                            i₃₉ < 100000
                                                                                                            && x₄₀ == i₃₉
                                                                                                            && 0 <= i₃₉
                                                                                                            && i₃₉ < 0
                                                                                                            && a8[x₄₀] == a6₆₁[i₃₉])))
                                                                                            && (forall x₄₀: int ::
                                                                                                    (exists i₃₉: int ::
                                                                                                            x₄₀ == i₃₉
                                                                                                            && 0 <= i₃₉
                                                                                                            && i₃₉ < 0)
                                                                                                    || a8[x₄₀] == a8[x₄₀])
                                                                                            && (forall i₃₉: int ::
                                                                                                  (  0 <= i₃₉
                                                                                                    && i₃₉ < 0
                                                                                                     ==> i₃₉ < 100000))
                                                                                            && (forall a8₆₃: [int]int, i₆₄: int ::
                                                                                                  (  0 <= i₆₄
                                                                                                    && i₆₄ <= 100000
                                                                                                    && (forall x₄₀: int, i₃₉: int ::
                                                                                                          (  x₄₀ == i₃₉
                                                                                                            && 0 <= i₃₉
                                                                                                            && i₃₉ < i₆₄
                                                                                                             ==> (exists i₃₉: int ::
                                                                                                                    i₃₉ < 100000
                                                                                                                    && x₄₀ == i₃₉
                                                                                                                    && 0 <= i₃₉
                                                                                                                    && i₃₉ < i₆₄
                                                                                                                    && a8₆₃[x₄₀] == a6₆₁[i₃₉])))
                                                                                                    && (forall x₄₀: int ::
                                                                                                            (exists i₃₉: int ::
                                                                                                                    x₄₀ == i₃₉
                                                                                                                    && 0 <= i₃₉
                                                                                                                    && i₃₉ < i₆₄)
                                                                                                            || a8₆₃[x₄₀] == a8[x₄₀])
                                                                                                    && (forall i₃₉: int ::
                                                                                                          (  0 <= i₃₉
                                                                                                            && i₃₉ < i₆₄
                                                                                                             ==> i₃₉ < 100000))
                                                                                                     ==> (i₆₄ < 100000
                                                                                                         ==> 0 <= i₆₄ + 1
                                                                                                          && i₆₄ + 1 <= 100000
                                                                                                          && (forall x₄₀: int, i₃₉: int ::
                                                                                                                (  x₄₀ == i₃₉
                                                                                                                  && 0 <= i₃₉
                                                                                                                  && i₃₉ < i₆₄ + 1
                                                                                                                   ==> (exists i₃₉: int ::
                                                                                                                          i₃₉ < 100000
                                                                                                                          && x₄₀ == i₃₉
                                                                                                                          && 0 <= i₃₉
                                                                                                                          && i₃₉ < i₆₄ + 1
                                                                                                                          && a8₆₃[i₆₄ := a6₆₁[i₆₄]][x₄₀] == a6₆₁[i₃₉])))
                                                                                                          && (forall x₄₀: int ::
                                                                                                                  (exists i₃₉: int ::
                                                                                                                          x₄₀ == i₃₉
                                                                                                                          && 0 <= i₃₉
                                                                                                                          && i₃₉ < i₆₄ + 1)
                                                                                                                  || a8₆₃[i₆₄ := a6₆₁[i₆₄]][x₄₀] == a8[x₄₀])
                                                                                                          && (forall i₃₉: int ::
                                                                                                                (  0 <= i₃₉
                                                                                                                  && i₃₉ < i₆₄ + 1
                                                                                                                   ==> i₃₉ < 100000)))
                                                                                                      &&   i₆₄ < 100000
                                                                                                        ||   0 <= 0
                                                                                                          && 0 <= 100000
                                                                                                          && (forall x₄₄: int, i₄₃: int ::
                                                                                                                (  x₄₄ == i₄₃
                                                                                                                  && 0 <= i₄₃
                                                                                                                  && i₄₃ < 0
                                                                                                                   ==> (exists i₄₃: int ::
                                                                                                                          i₄₃ < 100000
                                                                                                                          && x₄₄ == i₄₃
                                                                                                                          && 0 <= i₄₃
                                                                                                                          && i₄₃ < 0
                                                                                                                          && a8₆₃[x₄₄] == a7₅₁[i₄₃])))
                                                                                                          && (forall x₄₄: int ::
                                                                                                                  (exists i₄₃: int ::
                                                                                                                          x₄₄ == i₄₃
                                                                                                                          && 0 <= i₄₃
                                                                                                                          && i₄₃ < 0)
                                                                                                                  || a8₆₃[x₄₄] == a8₆₃[x₄₄])
                                                                                                          && (forall i₄₃: int ::
                                                                                                                (  0 <= i₄₃
                                                                                                                  && i₄₃ < 0
                                                                                                                   ==> i₄₃ < 100000))
                                                                                                          && (forall a8₆₅: [int]int, i₆₆: int ::
                                                                                                                (  0 <= i₆₆
                                                                                                                  && i₆₆ <= 100000
                                                                                                                  && (forall x₄₄: int, i₄₃: int ::
                                                                                                                        (  x₄₄ == i₄₃
                                                                                                                          && 0 <= i₄₃
                                                                                                                          && i₄₃ < i₆₆
                                                                                                                           ==> (exists i₄₃: int ::
                                                                                                                                  i₄₃ < 100000
                                                                                                                                  && x₄₄ == i₄₃
                                                                                                                                  && 0 <= i₄₃
                                                                                                                                  && i₄₃ < i₆₆
                                                                                                                                  && a8₆₅[x₄₄] == a7₅₁[i₄₃])))
                                                                                                                  && (forall x₄₄: int ::
                                                                                                                          (exists i₄₃: int ::
                                                                                                                                  x₄₄ == i₄₃
                                                                                                                                  && 0 <= i₄₃
                                                                                                                                  && i₄₃ < i₆₆)
                                                                                                                          || a8₆₅[x₄₄] == a8₆₃[x₄₄])
                                                                                                                  && (forall i₄₃: int ::
                                                                                                                        (  0 <= i₄₃
                                                                                                                          && i₄₃ < i₆₆
                                                                                                                           ==> i₄₃ < 100000))
                                                                                                                   ==> (i₆₆ < 100000
                                                                                                                       ==> 0 <= i₆₆ + 1
                                                                                                                        && i₆₆ + 1 <= 100000
                                                                                                                        && (forall x₄₄: int, i₄₃: int ::
                                                                                                                              (  x₄₄ == i₄₃
                                                                                                                                && 0 <= i₄₃
                                                                                                                                && i₄₃ < i₆₆ + 1
                                                                                                                                 ==> (exists i₄₃: int ::
                                                                                                                                        i₄₃ < 100000
                                                                                                                                        && x₄₄ == i₄₃
                                                                                                                                        && 0 <= i₄₃
                                                                                                                                        && i₄₃ < i₆₆ + 1
                                                                                                                                        && a8₆₅[i₆₆ := a7₅₁[i₆₆]][x₄₄] == a7₅₁[i₄₃])))
                                                                                                                        && (forall x₄₄: int ::
                                                                                                                                (exists i₄₃: int ::
                                                                                                                                        x₄₄ == i₄₃
                                                                                                                                        && 0 <= i₄₃
                                                                                                                                        && i₄₃ < i₆₆ + 1)
                                                                                                                                || a8₆₅[i₆₆ := a7₅₁[i₆₆]][x₄₄] == a8₆₃[x₄₄])
                                                                                                                        && (forall i₄₃: int ::
                                                                                                                              (  0 <= i₄₃
                                                                                                                                && i₄₃ < i₆₆ + 1
                                                                                                                                 ==> i₄₃ < 100000)))
                                                                                                                    &&   i₆₆ < 100000
                                                                                                                      ||   0 <= 0
                                                                                                                        && 0 <= 100000
                                                                                                                        && (forall x₄₈: int ::
                                                                                                                              (  0 <= x₄₈
                                                                                                                                && x₄₈ < 0
                                                                                                                                 ==> x₄₈ < 100000))
                                                                                                                        && (forall x₆₇: int ::
                                                                                                                              (  0 <= x₆₇
                                                                                                                                && x₆₇ <= 100000
                                                                                                                                && (forall x₄₈: int ::
                                                                                                                                      (  0 <= x₄₈
                                                                                                                                        && x₄₈ < x₆₇
                                                                                                                                         ==> x₄₈ < 100000))
                                                                                                                                 ==> (x₆₇ < 100000
                                                                                                                                   ==> a1₅₀[x₆₇] == a8₆₅[x₆₇]
                                                                                                                                    && 0 <= x₆₇ + 1
                                                                                                                                    && x₆₇ + 1 <= 100000
                                                                                                                                    && (forall x₄₈: int ::
                                                                                                                                          (  0 <= x₄₈
                                                                                                                                            && x₄₈ < x₆₇ + 1
                                                                                                                                             ==> x₄₈ < 100000))))))))))))))))))))));


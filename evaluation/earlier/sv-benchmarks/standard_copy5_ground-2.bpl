data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int, a3: [int]int, a4: [int]int, a5: [int]int, a6: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₁₁: int, a₁₀: int ::
              (  x₁₁ == a₁₀
                && 0 <= a₁₀
                && a₁₀ < 0
                 ==> (exists __VERIFIER_nondet_int₁₈: int, a₁₀: int ::
                        a₁₀ < 100000
                        && x₁₁ == a₁₀
                        && 0 <= a₁₀
                        && a₁₀ < 0
                        && a1[x₁₁] == __VERIFIER_nondet_int₁₈)))
        && (forall x₁₁: int ::
                (exists a₁₀: int ::
                        x₁₁ == a₁₀
                        && 0 <= a₁₀
                        && a₁₀ < 0)
                || a1[x₁₁] == a1[x₁₁])
        && (forall x₁₂: int, a₁₀: int ::
              (  x₁₂ == a₁₀
                && 0 <= a₁₀
                && a₁₀ < 0
                 ==> (exists __VERIFIER_nondet_int₂₉: int, a₁₀: int ::
                        a₁₀ < 100000
                        && x₁₂ == a₁₀
                        && 0 <= a₁₀
                        && a₁₀ < 0
                        && a5[x₁₂] == __VERIFIER_nondet_int₂₉)))
        && (forall x₁₂: int ::
                (exists a₁₀: int ::
                        x₁₂ == a₁₀
                        && 0 <= a₁₀
                        && a₁₀ < 0)
                || a5[x₁₂] == a5[x₁₂])
        && (forall a₁₀: int ::
              (  0 <= a₁₀
                && a₁₀ < 0
                 ==> a₁₀ < 100000))
        && (forall a1₄₀: [int]int, a5₄₁: [int]int, a₄₂: int ::
              (  0 <= a₄₂
                && a₄₂ <= 100000
                && (forall x₁₁: int, a₁₀: int ::
                      (  x₁₁ == a₁₀
                        && 0 <= a₁₀
                        && a₁₀ < a₄₂
                         ==> (exists __VERIFIER_nondet_int₁₈: int, a₁₀: int ::
                                a₁₀ < 100000
                                && x₁₁ == a₁₀
                                && 0 <= a₁₀
                                && a₁₀ < a₄₂
                                && a1₄₀[x₁₁] == __VERIFIER_nondet_int₁₈)))
                && (forall x₁₁: int ::
                        (exists a₁₀: int ::
                                x₁₁ == a₁₀
                                && 0 <= a₁₀
                                && a₁₀ < a₄₂)
                        || a1₄₀[x₁₁] == a1[x₁₁])
                && (forall x₁₂: int, a₁₀: int ::
                      (  x₁₂ == a₁₀
                        && 0 <= a₁₀
                        && a₁₀ < a₄₂
                         ==> (exists __VERIFIER_nondet_int₂₉: int, a₁₀: int ::
                                a₁₀ < 100000
                                && x₁₂ == a₁₀
                                && 0 <= a₁₀
                                && a₁₀ < a₄₂
                                && a5₄₁[x₁₂] == __VERIFIER_nondet_int₂₉)))
                && (forall x₁₂: int ::
                        (exists a₁₀: int ::
                                x₁₂ == a₁₀
                                && 0 <= a₁₀
                                && a₁₀ < a₄₂)
                        || a5₄₁[x₁₂] == a5[x₁₂])
                && (forall a₁₀: int ::
                      (  0 <= a₁₀
                        && a₁₀ < a₄₂
                         ==> a₁₀ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (a₄₂ < 100000
                           ==> 0 <= a₄₂ + 1
                            && a₄₂ + 1 <= 100000
                            && (forall x₁₁: int, a₁₀: int ::
                                  (  x₁₁ == a₁₀
                                    && 0 <= a₁₀
                                    && a₁₀ < a₄₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₈: int, a₁₀: int ::
                                            a₁₀ < 100000
                                            && x₁₁ == a₁₀
                                            && 0 <= a₁₀
                                            && a₁₀ < a₄₂ + 1
                                            && a1₄₀[a₄₂ := __VERIFIER_nondet_int₁][x₁₁] == __VERIFIER_nondet_int₁₈)))
                            && (forall x₁₁: int ::
                                    (exists a₁₀: int ::
                                            x₁₁ == a₁₀
                                            && 0 <= a₁₀
                                            && a₁₀ < a₄₂ + 1)
                                    || a1₄₀[a₄₂ := __VERIFIER_nondet_int₁][x₁₁] == a1[x₁₁])
                            && (forall x₁₂: int, a₁₀: int ::
                                  (  x₁₂ == a₁₀
                                    && 0 <= a₁₀
                                    && a₁₀ < a₄₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₉: int, a₁₀: int ::
                                            a₁₀ < 100000
                                            && x₁₂ == a₁₀
                                            && 0 <= a₁₀
                                            && a₁₀ < a₄₂ + 1
                                            && a5₄₁[a₄₂ := __VERIFIER_nondet_int₂][x₁₂] == __VERIFIER_nondet_int₂₉)))
                            && (forall x₁₂: int ::
                                    (exists a₁₀: int ::
                                            x₁₂ == a₁₀
                                            && 0 <= a₁₀
                                            && a₁₀ < a₄₂ + 1)
                                    || a5₄₁[a₄₂ := __VERIFIER_nondet_int₂][x₁₂] == a5[x₁₂])
                            && (forall a₁₀: int ::
                                  (  0 <= a₁₀
                                    && a₁₀ < a₄₂ + 1
                                     ==> a₁₀ < 100000))))
                  &&   a₄₂ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₁₈: int, i₁₇: int ::
                            (  x₁₈ == i₁₇
                              && 0 <= i₁₇
                              && i₁₇ < 0
                               ==> (exists i₁₇: int ::
                                      i₁₇ < 100000
                                      && x₁₈ == i₁₇
                                      && 0 <= i₁₇
                                      && i₁₇ < 0
                                      && a2[x₁₈] == a1₄₀[i₁₇])))
                      && (forall x₁₈: int ::
                              (exists i₁₇: int ::
                                      x₁₈ == i₁₇
                                      && 0 <= i₁₇
                                      && i₁₇ < 0)
                              || a2[x₁₈] == a2[x₁₈])
                      && (forall i₁₇: int ::
                            (  0 <= i₁₇
                              && i₁₇ < 0
                               ==> i₁₇ < 100000))
                      && (forall a2₄₃: [int]int, i₄₄: int ::
                            (  0 <= i₄₄
                              && i₄₄ <= 100000
                              && (forall x₁₈: int, i₁₇: int ::
                                    (  x₁₈ == i₁₇
                                      && 0 <= i₁₇
                                      && i₁₇ < i₄₄
                                       ==> (exists i₁₇: int ::
                                              i₁₇ < 100000
                                              && x₁₈ == i₁₇
                                              && 0 <= i₁₇
                                              && i₁₇ < i₄₄
                                              && a2₄₃[x₁₈] == a1₄₀[i₁₇])))
                              && (forall x₁₈: int ::
                                      (exists i₁₇: int ::
                                              x₁₈ == i₁₇
                                              && 0 <= i₁₇
                                              && i₁₇ < i₄₄)
                                      || a2₄₃[x₁₈] == a2[x₁₈])
                              && (forall i₁₇: int ::
                                    (  0 <= i₁₇
                                      && i₁₇ < i₄₄
                                       ==> i₁₇ < 100000))
                               ==> (i₄₄ < 100000
                                   ==> 0 <= i₄₄ + 1
                                    && i₄₄ + 1 <= 100000
                                    && (forall x₁₈: int, i₁₇: int ::
                                          (  x₁₈ == i₁₇
                                            && 0 <= i₁₇
                                            && i₁₇ < i₄₄ + 1
                                             ==> (exists i₁₇: int ::
                                                    i₁₇ < 100000
                                                    && x₁₈ == i₁₇
                                                    && 0 <= i₁₇
                                                    && i₁₇ < i₄₄ + 1
                                                    && a2₄₃[i₄₄ := a1₄₀[i₄₄]][x₁₈] == a1₄₀[i₁₇])))
                                    && (forall x₁₈: int ::
                                            (exists i₁₇: int ::
                                                    x₁₈ == i₁₇
                                                    && 0 <= i₁₇
                                                    && i₁₇ < i₄₄ + 1)
                                            || a2₄₃[i₄₄ := a1₄₀[i₄₄]][x₁₈] == a2[x₁₈])
                                    && (forall i₁₇: int ::
                                          (  0 <= i₁₇
                                            && i₁₇ < i₄₄ + 1
                                             ==> i₁₇ < 100000)))
                                &&   i₄₄ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₂₂: int, i₂₁: int ::
                                          (  x₂₂ == i₂₁
                                            && 0 <= i₂₁
                                            && i₂₁ < 0
                                             ==> (exists i₂₁: int ::
                                                    i₂₁ < 100000
                                                    && x₂₂ == i₂₁
                                                    && 0 <= i₂₁
                                                    && i₂₁ < 0
                                                    && a3[x₂₂] == a2₄₃[i₂₁])))
                                    && (forall x₂₂: int ::
                                            (exists i₂₁: int ::
                                                    x₂₂ == i₂₁
                                                    && 0 <= i₂₁
                                                    && i₂₁ < 0)
                                            || a3[x₂₂] == a3[x₂₂])
                                    && (forall i₂₁: int ::
                                          (  0 <= i₂₁
                                            && i₂₁ < 0
                                             ==> i₂₁ < 100000))
                                    && (forall a3₄₅: [int]int, i₄₆: int ::
                                          (  0 <= i₄₆
                                            && i₄₆ <= 100000
                                            && (forall x₂₂: int, i₂₁: int ::
                                                  (  x₂₂ == i₂₁
                                                    && 0 <= i₂₁
                                                    && i₂₁ < i₄₆
                                                     ==> (exists i₂₁: int ::
                                                            i₂₁ < 100000
                                                            && x₂₂ == i₂₁
                                                            && 0 <= i₂₁
                                                            && i₂₁ < i₄₆
                                                            && a3₄₅[x₂₂] == a2₄₃[i₂₁])))
                                            && (forall x₂₂: int ::
                                                    (exists i₂₁: int ::
                                                            x₂₂ == i₂₁
                                                            && 0 <= i₂₁
                                                            && i₂₁ < i₄₆)
                                                    || a3₄₅[x₂₂] == a3[x₂₂])
                                            && (forall i₂₁: int ::
                                                  (  0 <= i₂₁
                                                    && i₂₁ < i₄₆
                                                     ==> i₂₁ < 100000))
                                             ==> (i₄₆ < 100000
                                                 ==> 0 <= i₄₆ + 1
                                                  && i₄₆ + 1 <= 100000
                                                  && (forall x₂₂: int, i₂₁: int ::
                                                        (  x₂₂ == i₂₁
                                                          && 0 <= i₂₁
                                                          && i₂₁ < i₄₆ + 1
                                                           ==> (exists i₂₁: int ::
                                                                  i₂₁ < 100000
                                                                  && x₂₂ == i₂₁
                                                                  && 0 <= i₂₁
                                                                  && i₂₁ < i₄₆ + 1
                                                                  && a3₄₅[i₄₆ := a2₄₃[i₄₆]][x₂₂] == a2₄₃[i₂₁])))
                                                  && (forall x₂₂: int ::
                                                          (exists i₂₁: int ::
                                                                  x₂₂ == i₂₁
                                                                  && 0 <= i₂₁
                                                                  && i₂₁ < i₄₆ + 1)
                                                          || a3₄₅[i₄₆ := a2₄₃[i₄₆]][x₂₂] == a3[x₂₂])
                                                  && (forall i₂₁: int ::
                                                        (  0 <= i₂₁
                                                          && i₂₁ < i₄₆ + 1
                                                           ==> i₂₁ < 100000)))
                                              &&   i₄₆ < 100000
                                                ||   0 <= 0
                                                  && 0 <= 100000
                                                  && (forall x₂₆: int, i₂₅: int ::
                                                        (  x₂₆ == i₂₅
                                                          && 0 <= i₂₅
                                                          && i₂₅ < 0
                                                           ==> (exists i₂₅: int ::
                                                                  i₂₅ < 100000
                                                                  && x₂₆ == i₂₅
                                                                  && 0 <= i₂₅
                                                                  && i₂₅ < 0
                                                                  && a4[x₂₆] == a3₄₅[i₂₅])))
                                                  && (forall x₂₆: int ::
                                                          (exists i₂₅: int ::
                                                                  x₂₆ == i₂₅
                                                                  && 0 <= i₂₅
                                                                  && i₂₅ < 0)
                                                          || a4[x₂₆] == a4[x₂₆])
                                                  && (forall i₂₅: int ::
                                                        (  0 <= i₂₅
                                                          && i₂₅ < 0
                                                           ==> i₂₅ < 100000))
                                                  && (forall a4₄₇: [int]int, i₄₈: int ::
                                                        (  0 <= i₄₈
                                                          && i₄₈ <= 100000
                                                          && (forall x₂₆: int, i₂₅: int ::
                                                                (  x₂₆ == i₂₅
                                                                  && 0 <= i₂₅
                                                                  && i₂₅ < i₄₈
                                                                   ==> (exists i₂₅: int ::
                                                                          i₂₅ < 100000
                                                                          && x₂₆ == i₂₅
                                                                          && 0 <= i₂₅
                                                                          && i₂₅ < i₄₈
                                                                          && a4₄₇[x₂₆] == a3₄₅[i₂₅])))
                                                          && (forall x₂₆: int ::
                                                                  (exists i₂₅: int ::
                                                                          x₂₆ == i₂₅
                                                                          && 0 <= i₂₅
                                                                          && i₂₅ < i₄₈)
                                                                  || a4₄₇[x₂₆] == a4[x₂₆])
                                                          && (forall i₂₅: int ::
                                                                (  0 <= i₂₅
                                                                  && i₂₅ < i₄₈
                                                                   ==> i₂₅ < 100000))
                                                           ==> (i₄₈ < 100000
                                                               ==> 0 <= i₄₈ + 1
                                                                && i₄₈ + 1 <= 100000
                                                                && (forall x₂₆: int, i₂₅: int ::
                                                                      (  x₂₆ == i₂₅
                                                                        && 0 <= i₂₅
                                                                        && i₂₅ < i₄₈ + 1
                                                                         ==> (exists i₂₅: int ::
                                                                                i₂₅ < 100000
                                                                                && x₂₆ == i₂₅
                                                                                && 0 <= i₂₅
                                                                                && i₂₅ < i₄₈ + 1
                                                                                && a4₄₇[i₄₈ := a3₄₅[i₄₈]][x₂₆] == a3₄₅[i₂₅])))
                                                                && (forall x₂₆: int ::
                                                                        (exists i₂₅: int ::
                                                                                x₂₆ == i₂₅
                                                                                && 0 <= i₂₅
                                                                                && i₂₅ < i₄₈ + 1)
                                                                        || a4₄₇[i₄₈ := a3₄₅[i₄₈]][x₂₆] == a4[x₂₆])
                                                                && (forall i₂₅: int ::
                                                                      (  0 <= i₂₅
                                                                        && i₂₅ < i₄₈ + 1
                                                                         ==> i₂₅ < 100000)))
                                                            &&   i₄₈ < 100000
                                                              ||   0 <= 0
                                                                && 0 <= 100000
                                                                && (forall x₃₀: int, i₂₉: int ::
                                                                      (  x₃₀ == i₂₉
                                                                        && 0 <= i₂₉
                                                                        && i₂₉ < 0
                                                                         ==> (exists i₂₉: int ::
                                                                                i₂₉ < 100000
                                                                                && x₃₀ == i₂₉
                                                                                && 0 <= i₂₉
                                                                                && i₂₉ < 0
                                                                                && a6[x₃₀] == a4₄₇[i₂₉])))
                                                                && (forall x₃₀: int ::
                                                                        (exists i₂₉: int ::
                                                                                x₃₀ == i₂₉
                                                                                && 0 <= i₂₉
                                                                                && i₂₉ < 0)
                                                                        || a6[x₃₀] == a6[x₃₀])
                                                                && (forall i₂₉: int ::
                                                                      (  0 <= i₂₉
                                                                        && i₂₉ < 0
                                                                         ==> i₂₉ < 100000))
                                                                && (forall a6₄₉: [int]int, i₅₀: int ::
                                                                      (  0 <= i₅₀
                                                                        && i₅₀ <= 100000
                                                                        && (forall x₃₀: int, i₂₉: int ::
                                                                              (  x₃₀ == i₂₉
                                                                                && 0 <= i₂₉
                                                                                && i₂₉ < i₅₀
                                                                                 ==> (exists i₂₉: int ::
                                                                                        i₂₉ < 100000
                                                                                        && x₃₀ == i₂₉
                                                                                        && 0 <= i₂₉
                                                                                        && i₂₉ < i₅₀
                                                                                        && a6₄₉[x₃₀] == a4₄₇[i₂₉])))
                                                                        && (forall x₃₀: int ::
                                                                                (exists i₂₉: int ::
                                                                                        x₃₀ == i₂₉
                                                                                        && 0 <= i₂₉
                                                                                        && i₂₉ < i₅₀)
                                                                                || a6₄₉[x₃₀] == a6[x₃₀])
                                                                        && (forall i₂₉: int ::
                                                                              (  0 <= i₂₉
                                                                                && i₂₉ < i₅₀
                                                                                 ==> i₂₉ < 100000))
                                                                         ==> (i₅₀ < 100000
                                                                             ==> 0 <= i₅₀ + 1
                                                                              && i₅₀ + 1 <= 100000
                                                                              && (forall x₃₀: int, i₂₉: int ::
                                                                                    (  x₃₀ == i₂₉
                                                                                      && 0 <= i₂₉
                                                                                      && i₂₉ < i₅₀ + 1
                                                                                       ==> (exists i₂₉: int ::
                                                                                              i₂₉ < 100000
                                                                                              && x₃₀ == i₂₉
                                                                                              && 0 <= i₂₉
                                                                                              && i₂₉ < i₅₀ + 1
                                                                                              && a6₄₉[i₅₀ := a4₄₇[i₅₀]][x₃₀] == a4₄₇[i₂₉])))
                                                                              && (forall x₃₀: int ::
                                                                                      (exists i₂₉: int ::
                                                                                              x₃₀ == i₂₉
                                                                                              && 0 <= i₂₉
                                                                                              && i₂₉ < i₅₀ + 1)
                                                                                      || a6₄₉[i₅₀ := a4₄₇[i₅₀]][x₃₀] == a6[x₃₀])
                                                                              && (forall i₂₉: int ::
                                                                                    (  0 <= i₂₉
                                                                                      && i₂₉ < i₅₀ + 1
                                                                                       ==> i₂₉ < 100000)))
                                                                          &&   i₅₀ < 100000
                                                                            ||   0 <= 0
                                                                              && 0 <= 100000
                                                                              && (forall x₃₄: int, i₃₃: int ::
                                                                                    (  x₃₄ == i₃₃
                                                                                      && 0 <= i₃₃
                                                                                      && i₃₃ < 0
                                                                                       ==> (exists i₃₃: int ::
                                                                                              i₃₃ < 100000
                                                                                              && x₃₄ == i₃₃
                                                                                              && 0 <= i₃₃
                                                                                              && i₃₃ < 0
                                                                                              && a6₄₉[x₃₄] == a5₄₁[i₃₃])))
                                                                              && (forall x₃₄: int ::
                                                                                      (exists i₃₃: int ::
                                                                                              x₃₄ == i₃₃
                                                                                              && 0 <= i₃₃
                                                                                              && i₃₃ < 0)
                                                                                      || a6₄₉[x₃₄] == a6₄₉[x₃₄])
                                                                              && (forall i₃₃: int ::
                                                                                    (  0 <= i₃₃
                                                                                      && i₃₃ < 0
                                                                                       ==> i₃₃ < 100000))
                                                                              && (forall a6₅₁: [int]int, i₅₂: int ::
                                                                                    (  0 <= i₅₂
                                                                                      && i₅₂ <= 100000
                                                                                      && (forall x₃₄: int, i₃₃: int ::
                                                                                            (  x₃₄ == i₃₃
                                                                                              && 0 <= i₃₃
                                                                                              && i₃₃ < i₅₂
                                                                                               ==> (exists i₃₃: int ::
                                                                                                      i₃₃ < 100000
                                                                                                      && x₃₄ == i₃₃
                                                                                                      && 0 <= i₃₃
                                                                                                      && i₃₃ < i₅₂
                                                                                                      && a6₅₁[x₃₄] == a5₄₁[i₃₃])))
                                                                                      && (forall x₃₄: int ::
                                                                                              (exists i₃₃: int ::
                                                                                                      x₃₄ == i₃₃
                                                                                                      && 0 <= i₃₃
                                                                                                      && i₃₃ < i₅₂)
                                                                                              || a6₅₁[x₃₄] == a6₄₉[x₃₄])
                                                                                      && (forall i₃₃: int ::
                                                                                            (  0 <= i₃₃
                                                                                              && i₃₃ < i₅₂
                                                                                               ==> i₃₃ < 100000))
                                                                                       ==> (i₅₂ < 100000
                                                                                           ==> 0 <= i₅₂ + 1
                                                                                            && i₅₂ + 1 <= 100000
                                                                                            && (forall x₃₄: int, i₃₃: int ::
                                                                                                  (  x₃₄ == i₃₃
                                                                                                    && 0 <= i₃₃
                                                                                                    && i₃₃ < i₅₂ + 1
                                                                                                     ==> (exists i₃₃: int ::
                                                                                                            i₃₃ < 100000
                                                                                                            && x₃₄ == i₃₃
                                                                                                            && 0 <= i₃₃
                                                                                                            && i₃₃ < i₅₂ + 1
                                                                                                            && a6₅₁[i₅₂ := a5₄₁[i₅₂]][x₃₄] == a5₄₁[i₃₃])))
                                                                                            && (forall x₃₄: int ::
                                                                                                    (exists i₃₃: int ::
                                                                                                            x₃₄ == i₃₃
                                                                                                            && 0 <= i₃₃
                                                                                                            && i₃₃ < i₅₂ + 1)
                                                                                                    || a6₅₁[i₅₂ := a5₄₁[i₅₂]][x₃₄] == a6₄₉[x₃₄])
                                                                                            && (forall i₃₃: int ::
                                                                                                  (  0 <= i₃₃
                                                                                                    && i₃₃ < i₅₂ + 1
                                                                                                     ==> i₃₃ < 100000)))
                                                                                        &&   i₅₂ < 100000
                                                                                          ||   0 <= 0
                                                                                            && 0 <= 100000
                                                                                            && (forall x₃₈: int ::
                                                                                                  (  0 <= x₃₈
                                                                                                    && x₃₈ < 0
                                                                                                     ==> x₃₈ < 100000))
                                                                                            && (forall x₅₃: int ::
                                                                                                  (  0 <= x₅₃
                                                                                                    && x₅₃ <= 100000
                                                                                                    && (forall x₃₈: int ::
                                                                                                          (  0 <= x₃₈
                                                                                                            && x₃₈ < x₅₃
                                                                                                             ==> x₃₈ < 100000))
                                                                                                     ==> (x₅₃ < 100000
                                                                                                       ==> a1₄₀[x₅₃] == a6₅₁[x₅₃]
                                                                                                        && 0 <= x₅₃ + 1
                                                                                                        && x₅₃ + 1 <= 100000
                                                                                                        && (forall x₃₈: int ::
                                                                                                              (  0 <= x₃₈
                                                                                                                && x₃₈ < x₅₃ + 1
                                                                                                                 ==> x₃₈ < 100000))))))))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a1: [int]int, a2: [int]int, a3: [int]int, a4: [int]int, a5: [int]int, a6: [int]int, a7: [int]int, a8: [int]int, a9: [int]int, a0: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₁₅: int, a₁₄: int ::
              (  x₁₅ == a₁₄
                && 0 <= a₁₄
                && a₁₄ < 0
                 ==> (exists __VERIFIER_nondet_int₁₁₂: int, a₁₄: int ::
                        a₁₄ < 100000
                        && x₁₅ == a₁₄
                        && 0 <= a₁₄
                        && a₁₄ < 0
                        && a1[x₁₅] == __VERIFIER_nondet_int₁₁₂)))
        && (forall x₁₅: int ::
                (exists a₁₄: int ::
                        x₁₅ == a₁₄
                        && 0 <= a₁₄
                        && a₁₄ < 0)
                || a1[x₁₅] == a1[x₁₅])
        && (forall x₁₆: int, a₁₄: int ::
              (  x₁₆ == a₁₄
                && 0 <= a₁₄
                && a₁₄ < 0
                 ==> (exists __VERIFIER_nondet_int₂₁₃: int, a₁₄: int ::
                        a₁₄ < 100000
                        && x₁₆ == a₁₄
                        && 0 <= a₁₄
                        && a₁₄ < 0
                        && a9[x₁₆] == __VERIFIER_nondet_int₂₁₃)))
        && (forall x₁₆: int ::
                (exists a₁₄: int ::
                        x₁₆ == a₁₄
                        && 0 <= a₁₄
                        && a₁₄ < 0)
                || a9[x₁₆] == a9[x₁₆])
        && (forall a₁₄: int ::
              (  0 <= a₁₄
                && a₁₄ < 0
                 ==> a₁₄ < 100000))
        && (forall a1₆₀: [int]int, a9₆₁: [int]int, a₆₂: int ::
              (  0 <= a₆₂
                && a₆₂ <= 100000
                && (forall x₁₅: int, a₁₄: int ::
                      (  x₁₅ == a₁₄
                        && 0 <= a₁₄
                        && a₁₄ < a₆₂
                         ==> (exists __VERIFIER_nondet_int₁₁₂: int, a₁₄: int ::
                                a₁₄ < 100000
                                && x₁₅ == a₁₄
                                && 0 <= a₁₄
                                && a₁₄ < a₆₂
                                && a1₆₀[x₁₅] == __VERIFIER_nondet_int₁₁₂)))
                && (forall x₁₅: int ::
                        (exists a₁₄: int ::
                                x₁₅ == a₁₄
                                && 0 <= a₁₄
                                && a₁₄ < a₆₂)
                        || a1₆₀[x₁₅] == a1[x₁₅])
                && (forall x₁₆: int, a₁₄: int ::
                      (  x₁₆ == a₁₄
                        && 0 <= a₁₄
                        && a₁₄ < a₆₂
                         ==> (exists __VERIFIER_nondet_int₂₁₃: int, a₁₄: int ::
                                a₁₄ < 100000
                                && x₁₆ == a₁₄
                                && 0 <= a₁₄
                                && a₁₄ < a₆₂
                                && a9₆₁[x₁₆] == __VERIFIER_nondet_int₂₁₃)))
                && (forall x₁₆: int ::
                        (exists a₁₄: int ::
                                x₁₆ == a₁₄
                                && 0 <= a₁₄
                                && a₁₄ < a₆₂)
                        || a9₆₁[x₁₆] == a9[x₁₆])
                && (forall a₁₄: int ::
                      (  0 <= a₁₄
                        && a₁₄ < a₆₂
                         ==> a₁₄ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (a₆₂ < 100000
                           ==> 0 <= a₆₂ + 1
                            && a₆₂ + 1 <= 100000
                            && (forall x₁₅: int, a₁₄: int ::
                                  (  x₁₅ == a₁₄
                                    && 0 <= a₁₄
                                    && a₁₄ < a₆₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₁₂: int, a₁₄: int ::
                                            a₁₄ < 100000
                                            && x₁₅ == a₁₄
                                            && 0 <= a₁₄
                                            && a₁₄ < a₆₂ + 1
                                            && a1₆₀[a₆₂ := __VERIFIER_nondet_int₁][x₁₅] == __VERIFIER_nondet_int₁₁₂)))
                            && (forall x₁₅: int ::
                                    (exists a₁₄: int ::
                                            x₁₅ == a₁₄
                                            && 0 <= a₁₄
                                            && a₁₄ < a₆₂ + 1)
                                    || a1₆₀[a₆₂ := __VERIFIER_nondet_int₁][x₁₅] == a1[x₁₅])
                            && (forall x₁₆: int, a₁₄: int ::
                                  (  x₁₆ == a₁₄
                                    && 0 <= a₁₄
                                    && a₁₄ < a₆₂ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₁₃: int, a₁₄: int ::
                                            a₁₄ < 100000
                                            && x₁₆ == a₁₄
                                            && 0 <= a₁₄
                                            && a₁₄ < a₆₂ + 1
                                            && a9₆₁[a₆₂ := __VERIFIER_nondet_int₂][x₁₆] == __VERIFIER_nondet_int₂₁₃)))
                            && (forall x₁₆: int ::
                                    (exists a₁₄: int ::
                                            x₁₆ == a₁₄
                                            && 0 <= a₁₄
                                            && a₁₄ < a₆₂ + 1)
                                    || a9₆₁[a₆₂ := __VERIFIER_nondet_int₂][x₁₆] == a9[x₁₆])
                            && (forall a₁₄: int ::
                                  (  0 <= a₁₄
                                    && a₁₄ < a₆₂ + 1
                                     ==> a₁₄ < 100000))))
                  &&   a₆₂ < 100000
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
                                      && a2[x₂₂] == a1₆₀[i₂₁])))
                      && (forall x₂₂: int ::
                              (exists i₂₁: int ::
                                      x₂₂ == i₂₁
                                      && 0 <= i₂₁
                                      && i₂₁ < 0)
                              || a2[x₂₂] == a2[x₂₂])
                      && (forall i₂₁: int ::
                            (  0 <= i₂₁
                              && i₂₁ < 0
                               ==> i₂₁ < 100000))
                      && (forall a2₆₃: [int]int, i₆₄: int ::
                            (  0 <= i₆₄
                              && i₆₄ <= 100000
                              && (forall x₂₂: int, i₂₁: int ::
                                    (  x₂₂ == i₂₁
                                      && 0 <= i₂₁
                                      && i₂₁ < i₆₄
                                       ==> (exists i₂₁: int ::
                                              i₂₁ < 100000
                                              && x₂₂ == i₂₁
                                              && 0 <= i₂₁
                                              && i₂₁ < i₆₄
                                              && a2₆₃[x₂₂] == a1₆₀[i₂₁])))
                              && (forall x₂₂: int ::
                                      (exists i₂₁: int ::
                                              x₂₂ == i₂₁
                                              && 0 <= i₂₁
                                              && i₂₁ < i₆₄)
                                      || a2₆₃[x₂₂] == a2[x₂₂])
                              && (forall i₂₁: int ::
                                    (  0 <= i₂₁
                                      && i₂₁ < i₆₄
                                       ==> i₂₁ < 100000))
                               ==> (i₆₄ < 100000
                                   ==> 0 <= i₆₄ + 1
                                    && i₆₄ + 1 <= 100000
                                    && (forall x₂₂: int, i₂₁: int ::
                                          (  x₂₂ == i₂₁
                                            && 0 <= i₂₁
                                            && i₂₁ < i₆₄ + 1
                                             ==> (exists i₂₁: int ::
                                                    i₂₁ < 100000
                                                    && x₂₂ == i₂₁
                                                    && 0 <= i₂₁
                                                    && i₂₁ < i₆₄ + 1
                                                    && a2₆₃[i₆₄ := a1₆₀[i₆₄]][x₂₂] == a1₆₀[i₂₁])))
                                    && (forall x₂₂: int ::
                                            (exists i₂₁: int ::
                                                    x₂₂ == i₂₁
                                                    && 0 <= i₂₁
                                                    && i₂₁ < i₆₄ + 1)
                                            || a2₆₃[i₆₄ := a1₆₀[i₆₄]][x₂₂] == a2[x₂₂])
                                    && (forall i₂₁: int ::
                                          (  0 <= i₂₁
                                            && i₂₁ < i₆₄ + 1
                                             ==> i₂₁ < 100000)))
                                &&   i₆₄ < 100000
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
                                                    && a3[x₂₆] == a2₆₃[i₂₅])))
                                    && (forall x₂₆: int ::
                                            (exists i₂₅: int ::
                                                    x₂₆ == i₂₅
                                                    && 0 <= i₂₅
                                                    && i₂₅ < 0)
                                            || a3[x₂₆] == a3[x₂₆])
                                    && (forall i₂₅: int ::
                                          (  0 <= i₂₅
                                            && i₂₅ < 0
                                             ==> i₂₅ < 100000))
                                    && (forall a3₆₅: [int]int, i₆₆: int ::
                                          (  0 <= i₆₆
                                            && i₆₆ <= 100000
                                            && (forall x₂₆: int, i₂₅: int ::
                                                  (  x₂₆ == i₂₅
                                                    && 0 <= i₂₅
                                                    && i₂₅ < i₆₆
                                                     ==> (exists i₂₅: int ::
                                                            i₂₅ < 100000
                                                            && x₂₆ == i₂₅
                                                            && 0 <= i₂₅
                                                            && i₂₅ < i₆₆
                                                            && a3₆₅[x₂₆] == a2₆₃[i₂₅])))
                                            && (forall x₂₆: int ::
                                                    (exists i₂₅: int ::
                                                            x₂₆ == i₂₅
                                                            && 0 <= i₂₅
                                                            && i₂₅ < i₆₆)
                                                    || a3₆₅[x₂₆] == a3[x₂₆])
                                            && (forall i₂₅: int ::
                                                  (  0 <= i₂₅
                                                    && i₂₅ < i₆₆
                                                     ==> i₂₅ < 100000))
                                             ==> (i₆₆ < 100000
                                                 ==> 0 <= i₆₆ + 1
                                                  && i₆₆ + 1 <= 100000
                                                  && (forall x₂₆: int, i₂₅: int ::
                                                        (  x₂₆ == i₂₅
                                                          && 0 <= i₂₅
                                                          && i₂₅ < i₆₆ + 1
                                                           ==> (exists i₂₅: int ::
                                                                  i₂₅ < 100000
                                                                  && x₂₆ == i₂₅
                                                                  && 0 <= i₂₅
                                                                  && i₂₅ < i₆₆ + 1
                                                                  && a3₆₅[i₆₆ := a2₆₃[i₆₆]][x₂₆] == a2₆₃[i₂₅])))
                                                  && (forall x₂₆: int ::
                                                          (exists i₂₅: int ::
                                                                  x₂₆ == i₂₅
                                                                  && 0 <= i₂₅
                                                                  && i₂₅ < i₆₆ + 1)
                                                          || a3₆₅[i₆₆ := a2₆₃[i₆₆]][x₂₆] == a3[x₂₆])
                                                  && (forall i₂₅: int ::
                                                        (  0 <= i₂₅
                                                          && i₂₅ < i₆₆ + 1
                                                           ==> i₂₅ < 100000)))
                                              &&   i₆₆ < 100000
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
                                                                  && a4[x₃₀] == a3₆₅[i₂₉])))
                                                  && (forall x₃₀: int ::
                                                          (exists i₂₉: int ::
                                                                  x₃₀ == i₂₉
                                                                  && 0 <= i₂₉
                                                                  && i₂₉ < 0)
                                                          || a4[x₃₀] == a4[x₃₀])
                                                  && (forall i₂₉: int ::
                                                        (  0 <= i₂₉
                                                          && i₂₉ < 0
                                                           ==> i₂₉ < 100000))
                                                  && (forall a4₆₇: [int]int, i₆₈: int ::
                                                        (  0 <= i₆₈
                                                          && i₆₈ <= 100000
                                                          && (forall x₃₀: int, i₂₉: int ::
                                                                (  x₃₀ == i₂₉
                                                                  && 0 <= i₂₉
                                                                  && i₂₉ < i₆₈
                                                                   ==> (exists i₂₉: int ::
                                                                          i₂₉ < 100000
                                                                          && x₃₀ == i₂₉
                                                                          && 0 <= i₂₉
                                                                          && i₂₉ < i₆₈
                                                                          && a4₆₇[x₃₀] == a3₆₅[i₂₉])))
                                                          && (forall x₃₀: int ::
                                                                  (exists i₂₉: int ::
                                                                          x₃₀ == i₂₉
                                                                          && 0 <= i₂₉
                                                                          && i₂₉ < i₆₈)
                                                                  || a4₆₇[x₃₀] == a4[x₃₀])
                                                          && (forall i₂₉: int ::
                                                                (  0 <= i₂₉
                                                                  && i₂₉ < i₆₈
                                                                   ==> i₂₉ < 100000))
                                                           ==> (i₆₈ < 100000
                                                               ==> 0 <= i₆₈ + 1
                                                                && i₆₈ + 1 <= 100000
                                                                && (forall x₃₀: int, i₂₉: int ::
                                                                      (  x₃₀ == i₂₉
                                                                        && 0 <= i₂₉
                                                                        && i₂₉ < i₆₈ + 1
                                                                         ==> (exists i₂₉: int ::
                                                                                i₂₉ < 100000
                                                                                && x₃₀ == i₂₉
                                                                                && 0 <= i₂₉
                                                                                && i₂₉ < i₆₈ + 1
                                                                                && a4₆₇[i₆₈ := a3₆₅[i₆₈]][x₃₀] == a3₆₅[i₂₉])))
                                                                && (forall x₃₀: int ::
                                                                        (exists i₂₉: int ::
                                                                                x₃₀ == i₂₉
                                                                                && 0 <= i₂₉
                                                                                && i₂₉ < i₆₈ + 1)
                                                                        || a4₆₇[i₆₈ := a3₆₅[i₆₈]][x₃₀] == a4[x₃₀])
                                                                && (forall i₂₉: int ::
                                                                      (  0 <= i₂₉
                                                                        && i₂₉ < i₆₈ + 1
                                                                         ==> i₂₉ < 100000)))
                                                            &&   i₆₈ < 100000
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
                                                                                && a5[x₃₄] == a4₆₇[i₃₃])))
                                                                && (forall x₃₄: int ::
                                                                        (exists i₃₃: int ::
                                                                                x₃₄ == i₃₃
                                                                                && 0 <= i₃₃
                                                                                && i₃₃ < 0)
                                                                        || a5[x₃₄] == a5[x₃₄])
                                                                && (forall i₃₃: int ::
                                                                      (  0 <= i₃₃
                                                                        && i₃₃ < 0
                                                                         ==> i₃₃ < 100000))
                                                                && (forall a5₆₉: [int]int, i₇₀: int ::
                                                                      (  0 <= i₇₀
                                                                        && i₇₀ <= 100000
                                                                        && (forall x₃₄: int, i₃₃: int ::
                                                                              (  x₃₄ == i₃₃
                                                                                && 0 <= i₃₃
                                                                                && i₃₃ < i₇₀
                                                                                 ==> (exists i₃₃: int ::
                                                                                        i₃₃ < 100000
                                                                                        && x₃₄ == i₃₃
                                                                                        && 0 <= i₃₃
                                                                                        && i₃₃ < i₇₀
                                                                                        && a5₆₉[x₃₄] == a4₆₇[i₃₃])))
                                                                        && (forall x₃₄: int ::
                                                                                (exists i₃₃: int ::
                                                                                        x₃₄ == i₃₃
                                                                                        && 0 <= i₃₃
                                                                                        && i₃₃ < i₇₀)
                                                                                || a5₆₉[x₃₄] == a5[x₃₄])
                                                                        && (forall i₃₃: int ::
                                                                              (  0 <= i₃₃
                                                                                && i₃₃ < i₇₀
                                                                                 ==> i₃₃ < 100000))
                                                                         ==> (i₇₀ < 100000
                                                                             ==> 0 <= i₇₀ + 1
                                                                              && i₇₀ + 1 <= 100000
                                                                              && (forall x₃₄: int, i₃₃: int ::
                                                                                    (  x₃₄ == i₃₃
                                                                                      && 0 <= i₃₃
                                                                                      && i₃₃ < i₇₀ + 1
                                                                                       ==> (exists i₃₃: int ::
                                                                                              i₃₃ < 100000
                                                                                              && x₃₄ == i₃₃
                                                                                              && 0 <= i₃₃
                                                                                              && i₃₃ < i₇₀ + 1
                                                                                              && a5₆₉[i₇₀ := a4₆₇[i₇₀]][x₃₄] == a4₆₇[i₃₃])))
                                                                              && (forall x₃₄: int ::
                                                                                      (exists i₃₃: int ::
                                                                                              x₃₄ == i₃₃
                                                                                              && 0 <= i₃₃
                                                                                              && i₃₃ < i₇₀ + 1)
                                                                                      || a5₆₉[i₇₀ := a4₆₇[i₇₀]][x₃₄] == a5[x₃₄])
                                                                              && (forall i₃₃: int ::
                                                                                    (  0 <= i₃₃
                                                                                      && i₃₃ < i₇₀ + 1
                                                                                       ==> i₃₃ < 100000)))
                                                                          &&   i₇₀ < 100000
                                                                            ||   0 <= 0
                                                                              && 0 <= 100000
                                                                              && (forall x₃₈: int, i₃₇: int ::
                                                                                    (  x₃₈ == i₃₇
                                                                                      && 0 <= i₃₇
                                                                                      && i₃₇ < 0
                                                                                       ==> (exists i₃₇: int ::
                                                                                              i₃₇ < 100000
                                                                                              && x₃₈ == i₃₇
                                                                                              && 0 <= i₃₇
                                                                                              && i₃₇ < 0
                                                                                              && a6[x₃₈] == a5₆₉[i₃₇])))
                                                                              && (forall x₃₈: int ::
                                                                                      (exists i₃₇: int ::
                                                                                              x₃₈ == i₃₇
                                                                                              && 0 <= i₃₇
                                                                                              && i₃₇ < 0)
                                                                                      || a6[x₃₈] == a6[x₃₈])
                                                                              && (forall i₃₇: int ::
                                                                                    (  0 <= i₃₇
                                                                                      && i₃₇ < 0
                                                                                       ==> i₃₇ < 100000))
                                                                              && (forall a6₇₁: [int]int, i₇₂: int ::
                                                                                    (  0 <= i₇₂
                                                                                      && i₇₂ <= 100000
                                                                                      && (forall x₃₈: int, i₃₇: int ::
                                                                                            (  x₃₈ == i₃₇
                                                                                              && 0 <= i₃₇
                                                                                              && i₃₇ < i₇₂
                                                                                               ==> (exists i₃₇: int ::
                                                                                                      i₃₇ < 100000
                                                                                                      && x₃₈ == i₃₇
                                                                                                      && 0 <= i₃₇
                                                                                                      && i₃₇ < i₇₂
                                                                                                      && a6₇₁[x₃₈] == a5₆₉[i₃₇])))
                                                                                      && (forall x₃₈: int ::
                                                                                              (exists i₃₇: int ::
                                                                                                      x₃₈ == i₃₇
                                                                                                      && 0 <= i₃₇
                                                                                                      && i₃₇ < i₇₂)
                                                                                              || a6₇₁[x₃₈] == a6[x₃₈])
                                                                                      && (forall i₃₇: int ::
                                                                                            (  0 <= i₃₇
                                                                                              && i₃₇ < i₇₂
                                                                                               ==> i₃₇ < 100000))
                                                                                       ==> (i₇₂ < 100000
                                                                                           ==> 0 <= i₇₂ + 1
                                                                                            && i₇₂ + 1 <= 100000
                                                                                            && (forall x₃₈: int, i₃₇: int ::
                                                                                                  (  x₃₈ == i₃₇
                                                                                                    && 0 <= i₃₇
                                                                                                    && i₃₇ < i₇₂ + 1
                                                                                                     ==> (exists i₃₇: int ::
                                                                                                            i₃₇ < 100000
                                                                                                            && x₃₈ == i₃₇
                                                                                                            && 0 <= i₃₇
                                                                                                            && i₃₇ < i₇₂ + 1
                                                                                                            && a6₇₁[i₇₂ := a5₆₉[i₇₂]][x₃₈] == a5₆₉[i₃₇])))
                                                                                            && (forall x₃₈: int ::
                                                                                                    (exists i₃₇: int ::
                                                                                                            x₃₈ == i₃₇
                                                                                                            && 0 <= i₃₇
                                                                                                            && i₃₇ < i₇₂ + 1)
                                                                                                    || a6₇₁[i₇₂ := a5₆₉[i₇₂]][x₃₈] == a6[x₃₈])
                                                                                            && (forall i₃₇: int ::
                                                                                                  (  0 <= i₃₇
                                                                                                    && i₃₇ < i₇₂ + 1
                                                                                                     ==> i₃₇ < 100000)))
                                                                                        &&   i₇₂ < 100000
                                                                                          ||   0 <= 0
                                                                                            && 0 <= 100000
                                                                                            && (forall x₄₂: int, i₄₁: int ::
                                                                                                  (  x₄₂ == i₄₁
                                                                                                    && 0 <= i₄₁
                                                                                                    && i₄₁ < 0
                                                                                                     ==> (exists i₄₁: int ::
                                                                                                            i₄₁ < 100000
                                                                                                            && x₄₂ == i₄₁
                                                                                                            && 0 <= i₄₁
                                                                                                            && i₄₁ < 0
                                                                                                            && a7[x₄₂] == a6₇₁[i₄₁])))
                                                                                            && (forall x₄₂: int ::
                                                                                                    (exists i₄₁: int ::
                                                                                                            x₄₂ == i₄₁
                                                                                                            && 0 <= i₄₁
                                                                                                            && i₄₁ < 0)
                                                                                                    || a7[x₄₂] == a7[x₄₂])
                                                                                            && (forall i₄₁: int ::
                                                                                                  (  0 <= i₄₁
                                                                                                    && i₄₁ < 0
                                                                                                     ==> i₄₁ < 100000))
                                                                                            && (forall a7₇₃: [int]int, i₇₄: int ::
                                                                                                  (  0 <= i₇₄
                                                                                                    && i₇₄ <= 100000
                                                                                                    && (forall x₄₂: int, i₄₁: int ::
                                                                                                          (  x₄₂ == i₄₁
                                                                                                            && 0 <= i₄₁
                                                                                                            && i₄₁ < i₇₄
                                                                                                             ==> (exists i₄₁: int ::
                                                                                                                    i₄₁ < 100000
                                                                                                                    && x₄₂ == i₄₁
                                                                                                                    && 0 <= i₄₁
                                                                                                                    && i₄₁ < i₇₄
                                                                                                                    && a7₇₃[x₄₂] == a6₇₁[i₄₁])))
                                                                                                    && (forall x₄₂: int ::
                                                                                                            (exists i₄₁: int ::
                                                                                                                    x₄₂ == i₄₁
                                                                                                                    && 0 <= i₄₁
                                                                                                                    && i₄₁ < i₇₄)
                                                                                                            || a7₇₃[x₄₂] == a7[x₄₂])
                                                                                                    && (forall i₄₁: int ::
                                                                                                          (  0 <= i₄₁
                                                                                                            && i₄₁ < i₇₄
                                                                                                             ==> i₄₁ < 100000))
                                                                                                     ==> (i₇₄ < 100000
                                                                                                         ==> 0 <= i₇₄ + 1
                                                                                                          && i₇₄ + 1 <= 100000
                                                                                                          && (forall x₄₂: int, i₄₁: int ::
                                                                                                                (  x₄₂ == i₄₁
                                                                                                                  && 0 <= i₄₁
                                                                                                                  && i₄₁ < i₇₄ + 1
                                                                                                                   ==> (exists i₄₁: int ::
                                                                                                                          i₄₁ < 100000
                                                                                                                          && x₄₂ == i₄₁
                                                                                                                          && 0 <= i₄₁
                                                                                                                          && i₄₁ < i₇₄ + 1
                                                                                                                          && a7₇₃[i₇₄ := a6₇₁[i₇₄]][x₄₂] == a6₇₁[i₄₁])))
                                                                                                          && (forall x₄₂: int ::
                                                                                                                  (exists i₄₁: int ::
                                                                                                                          x₄₂ == i₄₁
                                                                                                                          && 0 <= i₄₁
                                                                                                                          && i₄₁ < i₇₄ + 1)
                                                                                                                  || a7₇₃[i₇₄ := a6₇₁[i₇₄]][x₄₂] == a7[x₄₂])
                                                                                                          && (forall i₄₁: int ::
                                                                                                                (  0 <= i₄₁
                                                                                                                  && i₄₁ < i₇₄ + 1
                                                                                                                   ==> i₄₁ < 100000)))
                                                                                                      &&   i₇₄ < 100000
                                                                                                        ||   0 <= 0
                                                                                                          && 0 <= 100000
                                                                                                          && (forall x₄₆: int, i₄₅: int ::
                                                                                                                (  x₄₆ == i₄₅
                                                                                                                  && 0 <= i₄₅
                                                                                                                  && i₄₅ < 0
                                                                                                                   ==> (exists i₄₅: int ::
                                                                                                                          i₄₅ < 100000
                                                                                                                          && x₄₆ == i₄₅
                                                                                                                          && 0 <= i₄₅
                                                                                                                          && i₄₅ < 0
                                                                                                                          && a8[x₄₆] == a7₇₃[i₄₅])))
                                                                                                          && (forall x₄₆: int ::
                                                                                                                  (exists i₄₅: int ::
                                                                                                                          x₄₆ == i₄₅
                                                                                                                          && 0 <= i₄₅
                                                                                                                          && i₄₅ < 0)
                                                                                                                  || a8[x₄₆] == a8[x₄₆])
                                                                                                          && (forall i₄₅: int ::
                                                                                                                (  0 <= i₄₅
                                                                                                                  && i₄₅ < 0
                                                                                                                   ==> i₄₅ < 100000))
                                                                                                          && (forall a8₇₅: [int]int, i₇₆: int ::
                                                                                                                (  0 <= i₇₆
                                                                                                                  && i₇₆ <= 100000
                                                                                                                  && (forall x₄₆: int, i₄₅: int ::
                                                                                                                        (  x₄₆ == i₄₅
                                                                                                                          && 0 <= i₄₅
                                                                                                                          && i₄₅ < i₇₆
                                                                                                                           ==> (exists i₄₅: int ::
                                                                                                                                  i₄₅ < 100000
                                                                                                                                  && x₄₆ == i₄₅
                                                                                                                                  && 0 <= i₄₅
                                                                                                                                  && i₄₅ < i₇₆
                                                                                                                                  && a8₇₅[x₄₆] == a7₇₃[i₄₅])))
                                                                                                                  && (forall x₄₆: int ::
                                                                                                                          (exists i₄₅: int ::
                                                                                                                                  x₄₆ == i₄₅
                                                                                                                                  && 0 <= i₄₅
                                                                                                                                  && i₄₅ < i₇₆)
                                                                                                                          || a8₇₅[x₄₆] == a8[x₄₆])
                                                                                                                  && (forall i₄₅: int ::
                                                                                                                        (  0 <= i₄₅
                                                                                                                          && i₄₅ < i₇₆
                                                                                                                           ==> i₄₅ < 100000))
                                                                                                                   ==> (i₇₆ < 100000
                                                                                                                       ==> 0 <= i₇₆ + 1
                                                                                                                        && i₇₆ + 1 <= 100000
                                                                                                                        && (forall x₄₆: int, i₄₅: int ::
                                                                                                                              (  x₄₆ == i₄₅
                                                                                                                                && 0 <= i₄₅
                                                                                                                                && i₄₅ < i₇₆ + 1
                                                                                                                                 ==> (exists i₄₅: int ::
                                                                                                                                        i₄₅ < 100000
                                                                                                                                        && x₄₆ == i₄₅
                                                                                                                                        && 0 <= i₄₅
                                                                                                                                        && i₄₅ < i₇₆ + 1
                                                                                                                                        && a8₇₅[i₇₆ := a7₇₃[i₇₆]][x₄₆] == a7₇₃[i₄₅])))
                                                                                                                        && (forall x₄₆: int ::
                                                                                                                                (exists i₄₅: int ::
                                                                                                                                        x₄₆ == i₄₅
                                                                                                                                        && 0 <= i₄₅
                                                                                                                                        && i₄₅ < i₇₆ + 1)
                                                                                                                                || a8₇₅[i₇₆ := a7₇₃[i₇₆]][x₄₆] == a8[x₄₆])
                                                                                                                        && (forall i₄₅: int ::
                                                                                                                              (  0 <= i₄₅
                                                                                                                                && i₄₅ < i₇₆ + 1
                                                                                                                                 ==> i₄₅ < 100000)))
                                                                                                                    &&   i₇₆ < 100000
                                                                                                                      ||   0 <= 0
                                                                                                                        && 0 <= 100000
                                                                                                                        && (forall x₅₀: int, i₄₉: int ::
                                                                                                                              (  x₅₀ == i₄₉
                                                                                                                                && 0 <= i₄₉
                                                                                                                                && i₄₉ < 0
                                                                                                                                 ==> (exists i₄₉: int ::
                                                                                                                                        i₄₉ < 100000
                                                                                                                                        && x₅₀ == i₄₉
                                                                                                                                        && 0 <= i₄₉
                                                                                                                                        && i₄₉ < 0
                                                                                                                                        && a0[x₅₀] == a8₇₅[i₄₉])))
                                                                                                                        && (forall x₅₀: int ::
                                                                                                                                (exists i₄₉: int ::
                                                                                                                                        x₅₀ == i₄₉
                                                                                                                                        && 0 <= i₄₉
                                                                                                                                        && i₄₉ < 0)
                                                                                                                                || a0[x₅₀] == a0[x₅₀])
                                                                                                                        && (forall i₄₉: int ::
                                                                                                                              (  0 <= i₄₉
                                                                                                                                && i₄₉ < 0
                                                                                                                                 ==> i₄₉ < 100000))
                                                                                                                        && (forall a0₇₇: [int]int, i₇₈: int ::
                                                                                                                              (  0 <= i₇₈
                                                                                                                                && i₇₈ <= 100000
                                                                                                                                && (forall x₅₀: int, i₄₉: int ::
                                                                                                                                      (  x₅₀ == i₄₉
                                                                                                                                        && 0 <= i₄₉
                                                                                                                                        && i₄₉ < i₇₈
                                                                                                                                         ==> (exists i₄₉: int ::
                                                                                                                                                i₄₉ < 100000
                                                                                                                                                && x₅₀ == i₄₉
                                                                                                                                                && 0 <= i₄₉
                                                                                                                                                && i₄₉ < i₇₈
                                                                                                                                                && a0₇₇[x₅₀] == a8₇₅[i₄₉])))
                                                                                                                                && (forall x₅₀: int ::
                                                                                                                                        (exists i₄₉: int ::
                                                                                                                                                x₅₀ == i₄₉
                                                                                                                                                && 0 <= i₄₉
                                                                                                                                                && i₄₉ < i₇₈)
                                                                                                                                        || a0₇₇[x₅₀] == a0[x₅₀])
                                                                                                                                && (forall i₄₉: int ::
                                                                                                                                      (  0 <= i₄₉
                                                                                                                                        && i₄₉ < i₇₈
                                                                                                                                         ==> i₄₉ < 100000))
                                                                                                                                 ==> (i₇₈ < 100000
                                                                                                                                     ==> 0 <= i₇₈ + 1
                                                                                                                                      && i₇₈ + 1 <= 100000
                                                                                                                                      && (forall x₅₀: int, i₄₉: int ::
                                                                                                                                            (  x₅₀ == i₄₉
                                                                                                                                              && 0 <= i₄₉
                                                                                                                                              && i₄₉ < i₇₈ + 1
                                                                                                                                               ==> (exists i₄₉: int ::
                                                                                                                                                      i₄₉ < 100000
                                                                                                                                                      && x₅₀ == i₄₉
                                                                                                                                                      && 0 <= i₄₉
                                                                                                                                                      && i₄₉ < i₇₈ + 1
                                                                                                                                                      && a0₇₇[i₇₈ := a8₇₅[i₇₈]][x₅₀] == a8₇₅[i₄₉])))
                                                                                                                                      && (forall x₅₀: int ::
                                                                                                                                              (exists i₄₉: int ::
                                                                                                                                                      x₅₀ == i₄₉
                                                                                                                                                      && 0 <= i₄₉
                                                                                                                                                      && i₄₉ < i₇₈ + 1)
                                                                                                                                              || a0₇₇[i₇₈ := a8₇₅[i₇₈]][x₅₀] == a0[x₅₀])
                                                                                                                                      && (forall i₄₉: int ::
                                                                                                                                            (  0 <= i₄₉
                                                                                                                                              && i₄₉ < i₇₈ + 1
                                                                                                                                               ==> i₄₉ < 100000)))
                                                                                                                                  &&   i₇₈ < 100000
                                                                                                                                    ||   0 <= 0
                                                                                                                                      && 0 <= 100000
                                                                                                                                      && (forall x₅₄: int, i₅₃: int ::
                                                                                                                                            (  x₅₄ == i₅₃
                                                                                                                                              && 0 <= i₅₃
                                                                                                                                              && i₅₃ < 0
                                                                                                                                               ==> (exists i₅₃: int ::
                                                                                                                                                      i₅₃ < 100000
                                                                                                                                                      && x₅₄ == i₅₃
                                                                                                                                                      && 0 <= i₅₃
                                                                                                                                                      && i₅₃ < 0
                                                                                                                                                      && a0₇₇[x₅₄] == a9₆₁[i₅₃])))
                                                                                                                                      && (forall x₅₄: int ::
                                                                                                                                              (exists i₅₃: int ::
                                                                                                                                                      x₅₄ == i₅₃
                                                                                                                                                      && 0 <= i₅₃
                                                                                                                                                      && i₅₃ < 0)
                                                                                                                                              || a0₇₇[x₅₄] == a0₇₇[x₅₄])
                                                                                                                                      && (forall i₅₃: int ::
                                                                                                                                            (  0 <= i₅₃
                                                                                                                                              && i₅₃ < 0
                                                                                                                                               ==> i₅₃ < 100000))
                                                                                                                                      && (forall a0₇₉: [int]int, i₈₀: int ::
                                                                                                                                            (  0 <= i₈₀
                                                                                                                                              && i₈₀ <= 100000
                                                                                                                                              && (forall x₅₄: int, i₅₃: int ::
                                                                                                                                                    (  x₅₄ == i₅₃
                                                                                                                                                      && 0 <= i₅₃
                                                                                                                                                      && i₅₃ < i₈₀
                                                                                                                                                       ==> (exists i₅₃: int ::
                                                                                                                                                              i₅₃ < 100000
                                                                                                                                                              && x₅₄ == i₅₃
                                                                                                                                                              && 0 <= i₅₃
                                                                                                                                                              && i₅₃ < i₈₀
                                                                                                                                                              && a0₇₉[x₅₄] == a9₆₁[i₅₃])))
                                                                                                                                              && (forall x₅₄: int ::
                                                                                                                                                      (exists i₅₃: int ::
                                                                                                                                                              x₅₄ == i₅₃
                                                                                                                                                              && 0 <= i₅₃
                                                                                                                                                              && i₅₃ < i₈₀)
                                                                                                                                                      || a0₇₉[x₅₄] == a0₇₇[x₅₄])
                                                                                                                                              && (forall i₅₃: int ::
                                                                                                                                                    (  0 <= i₅₃
                                                                                                                                                      && i₅₃ < i₈₀
                                                                                                                                                       ==> i₅₃ < 100000))
                                                                                                                                               ==> (i₈₀ < 100000
                                                                                                                                                   ==> 0 <= i₈₀ + 1
                                                                                                                                                    && i₈₀ + 1 <= 100000
                                                                                                                                                    && (forall x₅₄: int, i₅₃: int ::
                                                                                                                                                          (  x₅₄ == i₅₃
                                                                                                                                                            && 0 <= i₅₃
                                                                                                                                                            && i₅₃ < i₈₀ + 1
                                                                                                                                                             ==> (exists i₅₃: int ::
                                                                                                                                                                    i₅₃ < 100000
                                                                                                                                                                    && x₅₄ == i₅₃
                                                                                                                                                                    && 0 <= i₅₃
                                                                                                                                                                    && i₅₃ < i₈₀ + 1
                                                                                                                                                                    && a0₇₉[i₈₀ := a9₆₁[i₈₀]][x₅₄] == a9₆₁[i₅₃])))
                                                                                                                                                    && (forall x₅₄: int ::
                                                                                                                                                            (exists i₅₃: int ::
                                                                                                                                                                    x₅₄ == i₅₃
                                                                                                                                                                    && 0 <= i₅₃
                                                                                                                                                                    && i₅₃ < i₈₀ + 1)
                                                                                                                                                            || a0₇₉[i₈₀ := a9₆₁[i₈₀]][x₅₄] == a0₇₇[x₅₄])
                                                                                                                                                    && (forall i₅₃: int ::
                                                                                                                                                          (  0 <= i₅₃
                                                                                                                                                            && i₅₃ < i₈₀ + 1
                                                                                                                                                             ==> i₅₃ < 100000)))
                                                                                                                                                &&   i₈₀ < 100000
                                                                                                                                                  ||   0 <= 0
                                                                                                                                                    && 0 <= 100000
                                                                                                                                                    && (forall x₅₈: int ::
                                                                                                                                                          (  0 <= x₅₈
                                                                                                                                                            && x₅₈ < 0
                                                                                                                                                             ==> x₅₈ < 100000))
                                                                                                                                                    && (forall x₈₁: int ::
                                                                                                                                                          (  0 <= x₈₁
                                                                                                                                                            && x₈₁ <= 100000
                                                                                                                                                            && (forall x₅₈: int ::
                                                                                                                                                                  (  0 <= x₅₈
                                                                                                                                                                    && x₅₈ < x₈₁
                                                                                                                                                                     ==> x₅₈ < 100000))
                                                                                                                                                             ==> (x₈₁ < 100000
                                                                                                                                                               ==> a1₆₀[x₈₁] == a0₇₉[x₈₁]
                                                                                                                                                                && 0 <= x₈₁ + 1
                                                                                                                                                                && x₈₁ + 1 <= 100000
                                                                                                                                                                && (forall x₅₈: int ::
                                                                                                                                                                      (  0 <= x₅₈
                                                                                                                                                                        && x₅₈ < x₈₁ + 1
                                                                                                                                                                         ==> x₅₈ < 100000))))))))))))))))))))))))));


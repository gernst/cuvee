data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall array: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₈: int, i₇: int ::
              (  x₈ == i₇
                && 0 <= i₇
                && i₇ < 0
                 ==> (exists __VERIFIER_nondet_int₁₆: int, i₇: int ::
                        i₇ < 100000
                        && x₈ == i₇
                        && 0 <= i₇
                        && i₇ < 0
                        && array[x₈] == __VERIFIER_nondet_int₁₆)))
        && (forall x₈: int ::
                (exists i₇: int ::
                        x₈ == i₇
                        && 0 <= i₇
                        && i₇ < 0)
                || array[x₈] == array[x₈])
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < 0
                 ==> i₇ < 100000))
        && (forall array₂₈: [int]int, i₂₉: int ::
              (  0 <= i₂₉
                && i₂₉ <= 100000
                && (forall x₈: int, i₇: int ::
                      (  x₈ == i₇
                        && 0 <= i₇
                        && i₇ < i₂₉
                         ==> (exists __VERIFIER_nondet_int₁₆: int, i₇: int ::
                                i₇ < 100000
                                && x₈ == i₇
                                && 0 <= i₇
                                && i₇ < i₂₉
                                && array₂₈[x₈] == __VERIFIER_nondet_int₁₆)))
                && (forall x₈: int ::
                        (exists i₇: int ::
                                x₈ == i₇
                                && 0 <= i₇
                                && i₇ < i₂₉)
                        || array₂₈[x₈] == array[x₈])
                && (forall i₇: int ::
                      (  0 <= i₇
                        && i₇ < i₂₉
                         ==> i₇ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (i₂₉ < 100000
                           ==> 0 <= i₂₉ + 1
                            && i₂₉ + 1 <= 100000
                            && (forall x₈: int, i₇: int ::
                                  (  x₈ == i₇
                                    && 0 <= i₇
                                    && i₇ < i₂₉ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₆: int, i₇: int ::
                                            i₇ < 100000
                                            && x₈ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₂₉ + 1
                                            && array₂₈[i₂₉ := __VERIFIER_nondet_int₁][x₈] == __VERIFIER_nondet_int₁₆)))
                            && (forall x₈: int ::
                                    (exists i₇: int ::
                                            x₈ == i₇
                                            && 0 <= i₇
                                            && i₇ < i₂₉ + 1)
                                    || array₂₈[i₂₉ := __VERIFIER_nondet_int₁][x₈] == array[x₈])
                            && (forall i₇: int ::
                                  (  0 <= i₇
                                    && i₇ < i₂₉ + 1
                                     ==> i₇ < 100000))))
                  &&   i₂₉ < 100000
                    ||   (array₂₈[0] < array₂₈[1]
                         ==> 2 <= 2
                          && 2 <= 100000
                          && (forall i₁₃: int ::
                                (  2 <= i₁₃
                                  && i₁₃ < 2
                                   ==> i₁₃ < 100000))
                          && (forall largest2₃₀: int, largest1₃₁: int, i₃₂: int ::
                                (  2 <= i₃₂
                                  && i₃₂ <= 100000
                                  && (forall i₁₃: int ::
                                        (  2 <= i₁₃
                                          && i₁₃ < i₃₂
                                           ==> i₁₃ < 100000))
                                   ==> (i₃₂ < 100000
                                       ==> (largest1₃₁ <= array₂₈[i₃₂]
                                           ==> 2 <= i₃₂ + 1
                                            && i₃₂ + 1 <= 100000
                                            && (forall i₁₃: int ::
                                                  (  2 <= i₁₃
                                                    && i₁₃ < i₃₂ + 1
                                                     ==> i₁₃ < 100000)))
                                        &&   largest1₃₁ <= array₂₈[i₃₂]
                                          ||   (largest2₃₀ < array₂₈[i₃₂]
                                               ==> 2 <= i₃₂ + 1
                                                && i₃₂ + 1 <= 100000
                                                && (forall i₁₃: int ::
                                                      (  2 <= i₁₃
                                                        && i₁₃ < i₃₂ + 1
                                                         ==> i₁₃ < 100000)))
                                            &&   largest2₃₀ < array₂₈[i₃₂]
                                              ||   2 <= i₃₂ + 1
                                                && i₃₂ + 1 <= 100000
                                                && (forall i₁₃: int ::
                                                      (  2 <= i₁₃
                                                        && i₁₃ < i₃₂ + 1
                                                         ==> i₁₃ < 100000)))
                                    &&   i₃₂ < 100000
                                      ||   0 <= 0
                                        && 0 <= 100000
                                        && (forall x₂₂: int ::
                                              (  0 <= x₂₂
                                                && x₂₂ < 0
                                                 ==> x₂₂ < 100000))
                                        && (forall x₃₃: int ::
                                              (  0 <= x₃₃
                                                && x₃₃ <= 100000
                                                && (forall x₂₂: int ::
                                                      (  0 <= x₂₂
                                                        && x₂₂ < x₃₃
                                                         ==> x₂₂ < 100000))
                                                 ==> (x₃₃ < 100000
                                                     ==> array₂₈[x₃₃] <= largest1₃₁
                                                      && 0 <= x₃₃ + 1
                                                      && x₃₃ + 1 <= 100000
                                                      && (forall x₂₂: int ::
                                                            (  0 <= x₂₂
                                                              && x₂₂ < x₃₃ + 1
                                                               ==> x₂₂ < 100000)))
                                                  &&   x₃₃ < 100000
                                                    ||   0 <= 0
                                                      && 0 <= 100000
                                                      && (forall x₂₅: int ::
                                                            (  0 <= x₂₅
                                                              && x₂₅ < 0
                                                               ==> x₂₅ < 100000))
                                                      && (forall x₃₄: int ::
                                                            (  0 <= x₃₄
                                                              && x₃₄ <= 100000
                                                              && (forall x₂₅: int ::
                                                                    (  0 <= x₂₅
                                                                      && x₂₅ < x₃₄
                                                                       ==> x₂₅ < 100000))
                                                               ==> (x₃₄ < 100000
                                                                 ==> array₂₈[x₃₄] <= largest2₃₀
                                                                    || array₂₈[x₃₄] == largest1₃₁
                                                                  && 0 <= x₃₄ + 1
                                                                  && x₃₄ + 1 <= 100000
                                                                  && (forall x₂₅: int ::
                                                                        (  0 <= x₂₅
                                                                          && x₂₅ < x₃₄ + 1
                                                                           ==> x₂₅ < 100000))))))))))
                      &&   array₂₈[0] < array₂₈[1]
                        ||   2 <= 2
                          && 2 <= 100000
                          && (forall i₁₃: int ::
                                (  2 <= i₁₃
                                  && i₁₃ < 2
                                   ==> i₁₃ < 100000))
                          && (forall largest2₄₆: int, largest1₄₇: int, i₄₈: int ::
                                (  2 <= i₄₈
                                  && i₄₈ <= 100000
                                  && (forall i₁₃: int ::
                                        (  2 <= i₁₃
                                          && i₁₃ < i₄₈
                                           ==> i₁₃ < 100000))
                                   ==> (i₄₈ < 100000
                                       ==> (largest1₄₇ <= array₂₈[i₄₈]
                                           ==> 2 <= i₄₈ + 1
                                            && i₄₈ + 1 <= 100000
                                            && (forall i₁₃: int ::
                                                  (  2 <= i₁₃
                                                    && i₁₃ < i₄₈ + 1
                                                     ==> i₁₃ < 100000)))
                                        &&   largest1₄₇ <= array₂₈[i₄₈]
                                          ||   (largest2₄₆ < array₂₈[i₄₈]
                                               ==> 2 <= i₄₈ + 1
                                                && i₄₈ + 1 <= 100000
                                                && (forall i₁₃: int ::
                                                      (  2 <= i₁₃
                                                        && i₁₃ < i₄₈ + 1
                                                         ==> i₁₃ < 100000)))
                                            &&   largest2₄₆ < array₂₈[i₄₈]
                                              ||   2 <= i₄₈ + 1
                                                && i₄₈ + 1 <= 100000
                                                && (forall i₁₃: int ::
                                                      (  2 <= i₁₃
                                                        && i₁₃ < i₄₈ + 1
                                                         ==> i₁₃ < 100000)))
                                    &&   i₄₈ < 100000
                                      ||   0 <= 0
                                        && 0 <= 100000
                                        && (forall x₂₂: int ::
                                              (  0 <= x₂₂
                                                && x₂₂ < 0
                                                 ==> x₂₂ < 100000))
                                        && (forall x₄₉: int ::
                                              (  0 <= x₄₉
                                                && x₄₉ <= 100000
                                                && (forall x₂₂: int ::
                                                      (  0 <= x₂₂
                                                        && x₂₂ < x₄₉
                                                         ==> x₂₂ < 100000))
                                                 ==> (x₄₉ < 100000
                                                     ==> array₂₈[x₄₉] <= largest1₄₇
                                                      && 0 <= x₄₉ + 1
                                                      && x₄₉ + 1 <= 100000
                                                      && (forall x₂₂: int ::
                                                            (  0 <= x₂₂
                                                              && x₂₂ < x₄₉ + 1
                                                               ==> x₂₂ < 100000)))
                                                  &&   x₄₉ < 100000
                                                    ||   0 <= 0
                                                      && 0 <= 100000
                                                      && (forall x₂₅: int ::
                                                            (  0 <= x₂₅
                                                              && x₂₅ < 0
                                                               ==> x₂₅ < 100000))
                                                      && (forall x₅₀: int ::
                                                            (  0 <= x₅₀
                                                              && x₅₀ <= 100000
                                                              && (forall x₂₅: int ::
                                                                    (  0 <= x₂₅
                                                                      && x₂₅ < x₅₀
                                                                       ==> x₂₅ < 100000))
                                                               ==> (x₅₀ < 100000
                                                                 ==> array₂₈[x₅₀] <= largest2₄₆
                                                                    || array₂₈[x₅₀] == largest1₄₇
                                                                  && 0 <= x₅₀ + 1
                                                                  && x₅₀ + 1 <= 100000
                                                                  && (forall x₂₅: int ::
                                                                        (  0 <= x₂₅
                                                                          && x₂₅ < x₅₀ + 1
                                                                           ==> x₂₅ < 100000))))))))))));


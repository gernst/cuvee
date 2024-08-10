data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₆: int, j₅: int ::
              (  x₆ == j₅
                && 0 <= j₅
                && j₅ < 0
                 ==> (exists __VERIFIER_nondet_int₁₃: int, j₅: int ::
                        j₅ < 100000
                        && x₆ == j₅
                        && 0 <= j₅
                        && j₅ < 0
                        && a[x₆] == __VERIFIER_nondet_int₁₃)))
        && (forall x₆: int ::
                (exists j₅: int ::
                        x₆ == j₅
                        && 0 <= j₅
                        && j₅ < 0)
                || a[x₆] == a[x₆])
        && (forall x₇: int, j₅: int ::
              (  x₇ == j₅
                && 0 <= j₅
                && j₅ < 0
                 ==> (exists __VERIFIER_nondet_int₂₄: int, j₅: int ::
                        j₅ < 100000
                        && x₇ == j₅
                        && 0 <= j₅
                        && j₅ < 0
                        && b[x₇] == __VERIFIER_nondet_int₂₄)))
        && (forall x₇: int ::
                (exists j₅: int ::
                        x₇ == j₅
                        && 0 <= j₅
                        && j₅ < 0)
                || b[x₇] == b[x₇])
        && (forall j₅: int ::
              (  0 <= j₅
                && j₅ < 0
                 ==> j₅ < 100000))
        && (forall a₁₈: [int]int, b₁₉: [int]int, j₂₀: int ::
              (  0 <= j₂₀
                && j₂₀ <= 100000
                && (forall x₆: int, j₅: int ::
                      (  x₆ == j₅
                        && 0 <= j₅
                        && j₅ < j₂₀
                         ==> (exists __VERIFIER_nondet_int₁₃: int, j₅: int ::
                                j₅ < 100000
                                && x₆ == j₅
                                && 0 <= j₅
                                && j₅ < j₂₀
                                && a₁₈[x₆] == __VERIFIER_nondet_int₁₃)))
                && (forall x₆: int ::
                        (exists j₅: int ::
                                x₆ == j₅
                                && 0 <= j₅
                                && j₅ < j₂₀)
                        || a₁₈[x₆] == a[x₆])
                && (forall x₇: int, j₅: int ::
                      (  x₇ == j₅
                        && 0 <= j₅
                        && j₅ < j₂₀
                         ==> (exists __VERIFIER_nondet_int₂₄: int, j₅: int ::
                                j₅ < 100000
                                && x₇ == j₅
                                && 0 <= j₅
                                && j₅ < j₂₀
                                && b₁₉[x₇] == __VERIFIER_nondet_int₂₄)))
                && (forall x₇: int ::
                        (exists j₅: int ::
                                x₇ == j₅
                                && 0 <= j₅
                                && j₅ < j₂₀)
                        || b₁₉[x₇] == b[x₇])
                && (forall j₅: int ::
                      (  0 <= j₅
                        && j₅ < j₂₀
                         ==> j₅ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (j₂₀ < 100000
                           ==> 0 <= j₂₀ + 1
                            && j₂₀ + 1 <= 100000
                            && (forall x₆: int, j₅: int ::
                                  (  x₆ == j₅
                                    && 0 <= j₅
                                    && j₅ < j₂₀ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₃: int, j₅: int ::
                                            j₅ < 100000
                                            && x₆ == j₅
                                            && 0 <= j₅
                                            && j₅ < j₂₀ + 1
                                            && a₁₈[j₂₀ := __VERIFIER_nondet_int₁][x₆] == __VERIFIER_nondet_int₁₃)))
                            && (forall x₆: int ::
                                    (exists j₅: int ::
                                            x₆ == j₅
                                            && 0 <= j₅
                                            && j₅ < j₂₀ + 1)
                                    || a₁₈[j₂₀ := __VERIFIER_nondet_int₁][x₆] == a[x₆])
                            && (forall x₇: int, j₅: int ::
                                  (  x₇ == j₅
                                    && 0 <= j₅
                                    && j₅ < j₂₀ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₄: int, j₅: int ::
                                            j₅ < 100000
                                            && x₇ == j₅
                                            && 0 <= j₅
                                            && j₅ < j₂₀ + 1
                                            && b₁₉[j₂₀ := __VERIFIER_nondet_int₂][x₇] == __VERIFIER_nondet_int₂₄)))
                            && (forall x₇: int ::
                                    (exists j₅: int ::
                                            x₇ == j₅
                                            && 0 <= j₅
                                            && j₅ < j₂₀ + 1)
                                    || b₁₉[j₂₀ := __VERIFIER_nondet_int₂][x₇] == b[x₇])
                            && (forall j₅: int ::
                                  (  0 <= j₅
                                    && j₅ < j₂₀ + 1
                                     ==> j₅ < 100000))))
                  &&   j₂₀ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall i₁₂: int ::
                            (  0 <= i₁₂
                              && i₁₂ < 0
                               ==> i₁₂ < 100000))
                      && (forall rv₂₁: int, i₂₂: int ::
                            (  0 <= i₂₂
                              && i₂₂ <= 100000
                              && (forall i₁₂: int ::
                                    (  0 <= i₁₂
                                      && i₁₂ < i₂₂
                                       ==> i₁₂ < 100000))
                               ==> (i₂₂ < 100000
                                   ==> a₁₈[i₂₂] == b₁₉[i₂₂]
                                      ||   0 <= i₂₂ + 1
                                        && i₂₂ + 1 <= 100000
                                        && (forall i₁₂: int ::
                                              (  0 <= i₁₂
                                                && i₁₂ < i₂₂ + 1
                                                 ==> i₁₂ < 100000))
                                    && (a₁₈[i₂₂] == b₁₉[i₂₂]
                                       ==> 0 <= i₂₂ + 1
                                        && i₂₂ + 1 <= 100000
                                        && (forall i₁₂: int ::
                                              (  0 <= i₁₂
                                                && i₁₂ < i₂₂ + 1
                                                 ==> i₁₂ < 100000))))
                                &&   i₂₂ < 100000
                                  || rv₂₁ == 0
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₁₆: int ::
                                          (  0 <= x₁₆
                                            && x₁₆ < 0
                                             ==> x₁₆ < 100000))
                                    && (forall x₂₃: int ::
                                          (  0 <= x₂₃
                                            && x₂₃ <= 100000
                                            && (forall x₁₆: int ::
                                                  (  0 <= x₁₆
                                                    && x₁₆ < x₂₃
                                                     ==> x₁₆ < 100000))
                                             ==> (x₂₃ < 100000
                                               ==> a₁₈[x₂₃] == b₁₉[x₂₃]
                                                && 0 <= x₂₃ + 1
                                                && x₂₃ + 1 <= 100000
                                                && (forall x₁₆: int ::
                                                      (  0 <= x₁₆
                                                        && x₁₆ < x₂₃ + 1
                                                         ==> x₁₆ < 100000))))))))));


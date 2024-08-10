data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 0 <= i₃
                && i₃ < 0
                 ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                        i₃ < 100000
                        && x₄ == i₃
                        && 0 <= i₃
                        && i₃ < 0
                        && a[x₄] == __VERIFIER_nondet_int₁₂)))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 0 <= i₃
                        && i₃ < 0)
                || a[x₄] == a[x₄])
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < 0
                 ==> i₃ < 100000))
        && (forall a₁₄: [int]int, i₁₅: int ::
              (  0 <= i₁₅
                && i₁₅ <= 100000
                && (forall x₄: int, i₃: int ::
                      (  x₄ == i₃
                        && 0 <= i₃
                        && i₃ < i₁₅
                         ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                                i₃ < 100000
                                && x₄ == i₃
                                && 0 <= i₃
                                && i₃ < i₁₅
                                && a₁₄[x₄] == __VERIFIER_nondet_int₁₂)))
                && (forall x₄: int ::
                        (exists i₃: int ::
                                x₄ == i₃
                                && 0 <= i₃
                                && i₃ < i₁₅)
                        || a₁₄[x₄] == a[x₄])
                && (forall i₃: int ::
                      (  0 <= i₃
                        && i₃ < i₁₅
                         ==> i₃ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (i₁₅ < 100000
                           ==> 0 <= i₁₅ + 1
                            && i₁₅ + 1 <= 100000
                            && (forall x₄: int, i₃: int ::
                                  (  x₄ == i₃
                                    && 0 <= i₃
                                    && i₃ < i₁₅ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                                            i₃ < 100000
                                            && x₄ == i₃
                                            && 0 <= i₃
                                            && i₃ < i₁₅ + 1
                                            && a₁₄[i₁₅ := __VERIFIER_nondet_int₁][x₄] == __VERIFIER_nondet_int₁₂)))
                            && (forall x₄: int ::
                                    (exists i₃: int ::
                                            x₄ == i₃
                                            && 0 <= i₃
                                            && i₃ < i₁₅ + 1)
                                    || a₁₄[i₁₅ := __VERIFIER_nondet_int₁][x₄] == a[x₄])
                            && (forall i₃: int ::
                                  (  0 <= i₃
                                    && i₃ < i₁₅ + 1
                                     ==> i₃ < 100000))))
                  &&   i₁₅ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall i₈: int ::
                            (  0 <= i₈
                              && i₈ < 0
                               ==> i₈ < 100000))
                      && (forall min₁₆: int, i₁₇: int ::
                            (  0 <= i₁₇
                              && i₁₇ <= 100000
                              && (forall i₈: int ::
                                    (  0 <= i₈
                                      && i₈ < i₁₇
                                       ==> i₈ < 100000))
                               ==> (i₁₇ < 100000
                                   ==> (a₁₄[i₁₇] < min₁₆
                                       ==> 0 <= i₁₇ + 1
                                        && i₁₇ + 1 <= 100000
                                        && (forall i₈: int ::
                                              (  0 <= i₈
                                                && i₈ < i₁₇ + 1
                                                 ==> i₈ < 100000)))
                                    &&   a₁₄[i₁₇] < min₁₆
                                      ||   0 <= i₁₇ + 1
                                        && i₁₇ + 1 <= 100000
                                        && (forall i₈: int ::
                                              (  0 <= i₈
                                                && i₈ < i₁₇ + 1
                                                 ==> i₈ < 100000)))
                                &&   i₁₇ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₁₂: int ::
                                          (  0 <= x₁₂
                                            && x₁₂ < 0
                                             ==> x₁₂ < 100000))
                                    && (forall x₁₈: int ::
                                          (  0 <= x₁₈
                                            && x₁₈ <= 100000
                                            && (forall x₁₂: int ::
                                                  (  0 <= x₁₂
                                                    && x₁₂ < x₁₈
                                                     ==> x₁₂ < 100000))
                                             ==> (x₁₈ < 100000
                                               ==> min₁₆ <= a₁₄[x₁₈]
                                                && 0 <= x₁₈ + 1
                                                && x₁₈ + 1 <= 100000
                                                && (forall x₁₂: int ::
                                                      (  0 <= x₁₂
                                                        && x₁₂ < x₁₈ + 1
                                                         ==> x₁₂ < 100000))))))))));


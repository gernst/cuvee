data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < 0
                 ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                        i₄ < 100000
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < 0
                        && a[x₅] == __VERIFIER_nondet_int₁₃)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < 0)
                || a[x₅] == a[x₅])
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < 0
                 ==> i₄ < 100000))
        && (forall a₂₅: [int]int, i₂₆: int ::
              (  0 <= i₂₆
                && i₂₆ <= 100000
                && (forall x₅: int, i₄: int ::
                      (  x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₂₆
                         ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                i₄ < 100000
                                && x₅ == i₄
                                && 0 <= i₄
                                && i₄ < i₂₆
                                && a₂₅[x₅] == __VERIFIER_nondet_int₁₃)))
                && (forall x₅: int ::
                        (exists i₄: int ::
                                x₅ == i₄
                                && 0 <= i₄
                                && i₄ < i₂₆)
                        || a₂₅[x₅] == a[x₅])
                && (forall i₄: int ::
                      (  0 <= i₄
                        && i₄ < i₂₆
                         ==> i₄ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (i₂₆ < 100000
                           ==> 0 <= i₂₆ + 1
                            && i₂₆ + 1 <= 100000
                            && (forall x₅: int, i₄: int ::
                                  (  x₅ == i₄
                                    && 0 <= i₄
                                    && i₄ < i₂₆ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₃: int, i₄: int ::
                                            i₄ < 100000
                                            && x₅ == i₄
                                            && 0 <= i₄
                                            && i₄ < i₂₆ + 1
                                            && a₂₅[i₂₆ := __VERIFIER_nondet_int₁][x₅] == __VERIFIER_nondet_int₁₃)))
                            && (forall x₅: int ::
                                    (exists i₄: int ::
                                            x₅ == i₄
                                            && 0 <= i₄
                                            && i₄ < i₂₆ + 1)
                                    || a₂₅[i₂₆ := __VERIFIER_nondet_int₁][x₅] == a[x₅])
                            && (forall i₄: int ::
                                  (  0 <= i₄
                                    && i₄ < i₂₆ + 1
                                     ==> i₄ < 100000))))
                  &&   i₂₆ < 100000
                    ||   1 <= 1
                      && 1 <= 100000
                      && (forall r₁₃: int, i₁₄: int ::
                            (  1 <= i₁₄
                              && i₁₄ < 1
                               ==> i₁₄ < 100000
                                && (r₁₃ == 0
                                   ==> false)))
                      && (forall r₂₇: int, i₂₈: int ::
                            (  1 <= i₂₈
                              && i₂₈ <= 100000
                              && (forall r₁₃: int, i₁₄: int ::
                                    (  1 <= i₁₄
                                      && i₁₄ < i₂₈
                                       ==> i₁₄ < 100000
                                        && (r₁₃ == 0
                                           ==> false)))
                               ==> (i₂₈ < 100000
                                   ==> r₂₇ == 0
                                    ||   i₂₈ - 1 <= -1 + i₂₈
                                      && 0 <= 1 + i₂₈ - 1
                                      && (forall r₉: int, j₁₀: int ::
                                            (  j₁₀ <= -1 + i₂₈
                                              && i₂₈ - 1 < j₁₀
                                               ==> 0 <= j₁₀
                                                && (r₉ == 0
                                                   ==> false)))
                                      && (forall r₃₅: int, j₃₆: int ::
                                            (  j₃₆ <= -1 + i₂₈
                                              && 0 <= 1 + j₃₆
                                              && (forall r₉: int, j₁₀: int ::
                                                    (  j₁₀ <= -1 + i₂₈
                                                      && j₃₆ < j₁₀
                                                       ==> 0 <= j₁₀
                                                        && (r₉ == 0
                                                           ==> false)))
                                               ==> (0 <= j₃₆
                                                   ==> r₃₅ == 0
                                                    ||   (a₂₅[i₂₈] == a₂₅[j₃₆]
                                                         ==> j₃₆ - 1 <= -1 + i₂₈
                                                          && 0 <= 1 + j₃₆ - 1
                                                          && (forall r₉: int, j₁₀: int ::
                                                                (  j₁₀ <= -1 + i₂₈
                                                                  && j₃₆ - 1 < j₁₀
                                                                   ==> 0 <= j₁₀
                                                                    && (r₉ == 0
                                                                       ==> false))))
                                                      &&   a₂₅[i₂₈] == a₂₅[j₃₆]
                                                        ||   j₃₆ - 1 <= -1 + i₂₈
                                                          && 0 <= 1 + j₃₆ - 1
                                                          && (forall r₉: int, j₁₀: int ::
                                                                (  j₁₀ <= -1 + i₂₈
                                                                  && j₃₆ - 1 < j₁₀
                                                                   ==> 0 <= j₁₀
                                                                    && (r₉ == 0
                                                                       ==> false))))
                                                &&     0 <= j₃₆
                                                    && (r₃₅ == 0
                                                       ==> false)
                                                  ||   1 <= i₂₈ + 1
                                                    && i₂₈ + 1 <= 100000
                                                    && (forall r₁₃: int, i₁₄: int ::
                                                          (  1 <= i₁₄
                                                            && i₁₄ < i₂₈ + 1
                                                             ==> i₁₄ < 100000
                                                              && (r₁₃ == 0
                                                                 ==> false))))))
                                &&     i₂₈ < 100000
                                    && (r₂₇ == 0
                                       ==> false)
                                  || r₂₇ == 0
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₂₂: int ::
                                          (  0 <= x₂₂
                                            && x₂₂ < 0
                                             ==> x₂₂ < 100000))
                                    && (forall x₃₀: int ::
                                          (  0 <= x₃₀
                                            && x₃₀ <= 100000
                                            && (forall x₂₂: int ::
                                                  (  0 <= x₂₂
                                                    && x₂₂ < x₃₀
                                                     ==> x₂₂ < 100000))
                                             ==> (x₃₀ < 100000
                                               ==> 1 + x₃₀ <= x₃₀ + 1
                                                && x₃₀ + 1 <= 100000
                                                && (forall y₁₉: int ::
                                                      (  1 + x₃₀ <= y₁₉
                                                        && y₁₉ < x₃₀ + 1
                                                         ==> y₁₉ < 100000))
                                                && (forall y₃₁: int ::
                                                      (  1 + x₃₀ <= y₃₁
                                                        && y₃₁ <= 100000
                                                        && (forall y₁₉: int ::
                                                              (  1 + x₃₀ <= y₁₉
                                                                && y₁₉ < y₃₁
                                                                 ==> y₁₉ < 100000))
                                                         ==> (y₃₁ < 100000
                                                             ==> (a₂₅[x₃₀] == a₂₅[y₃₁]
                                                               ==> false))
                                                          &&   y₃₁ < 100000
                                                            ||   0 <= x₃₀ + 1
                                                              && x₃₀ + 1 <= 100000
                                                              && (forall x₂₂: int ::
                                                                    (  0 <= x₂₂
                                                                      && x₂₂ < x₃₀ + 1
                                                                       ==> x₂₂ < 100000))))))))))));


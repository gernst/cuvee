data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int, c: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₇: int, j₆: int ::
              (  x₇ == j₆
                && 0 <= j₆
                && j₆ < 0
                 ==> (exists __VERIFIER_nondet_int₁₄: int, j₆: int ::
                        j₆ < 100000
                        && x₇ == j₆
                        && 0 <= j₆
                        && j₆ < 0
                        && a[x₇] == __VERIFIER_nondet_int₁₄)))
        && (forall x₇: int ::
                (exists j₆: int ::
                        x₇ == j₆
                        && 0 <= j₆
                        && j₆ < 0)
                || a[x₇] == a[x₇])
        && (forall x₈: int, j₆: int ::
              (  x₈ == j₆
                && 0 <= j₆
                && j₆ < 0
                 ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                        j₆ < 100000
                        && x₈ == j₆
                        && 0 <= j₆
                        && j₆ < 0
                        && b[x₈] == __VERIFIER_nondet_int₂₅)))
        && (forall x₈: int ::
                (exists j₆: int ::
                        x₈ == j₆
                        && 0 <= j₆
                        && j₆ < 0)
                || b[x₈] == b[x₈])
        && (forall j₆: int ::
              (  0 <= j₆
                && j₆ < 0
                 ==> j₆ < 100000))
        && (forall a₂₄: [int]int, b₂₅: [int]int, j₂₆: int ::
              (  0 <= j₂₆
                && j₂₆ <= 100000
                && (forall x₇: int, j₆: int ::
                      (  x₇ == j₆
                        && 0 <= j₆
                        && j₆ < j₂₆
                         ==> (exists __VERIFIER_nondet_int₁₄: int, j₆: int ::
                                j₆ < 100000
                                && x₇ == j₆
                                && 0 <= j₆
                                && j₆ < j₂₆
                                && a₂₄[x₇] == __VERIFIER_nondet_int₁₄)))
                && (forall x₇: int ::
                        (exists j₆: int ::
                                x₇ == j₆
                                && 0 <= j₆
                                && j₆ < j₂₆)
                        || a₂₄[x₇] == a[x₇])
                && (forall x₈: int, j₆: int ::
                      (  x₈ == j₆
                        && 0 <= j₆
                        && j₆ < j₂₆
                         ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                                j₆ < 100000
                                && x₈ == j₆
                                && 0 <= j₆
                                && j₆ < j₂₆
                                && b₂₅[x₈] == __VERIFIER_nondet_int₂₅)))
                && (forall x₈: int ::
                        (exists j₆: int ::
                                x₈ == j₆
                                && 0 <= j₆
                                && j₆ < j₂₆)
                        || b₂₅[x₈] == b[x₈])
                && (forall j₆: int ::
                      (  0 <= j₆
                        && j₆ < j₂₆
                         ==> j₆ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (j₂₆ < 100000
                           ==> 0 <= j₂₆ + 1
                            && j₂₆ + 1 <= 100000
                            && (forall x₇: int, j₆: int ::
                                  (  x₇ == j₆
                                    && 0 <= j₆
                                    && j₆ < j₂₆ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₄: int, j₆: int ::
                                            j₆ < 100000
                                            && x₇ == j₆
                                            && 0 <= j₆
                                            && j₆ < j₂₆ + 1
                                            && a₂₄[j₂₆ := __VERIFIER_nondet_int₁][x₇] == __VERIFIER_nondet_int₁₄)))
                            && (forall x₇: int ::
                                    (exists j₆: int ::
                                            x₇ == j₆
                                            && 0 <= j₆
                                            && j₆ < j₂₆ + 1)
                                    || a₂₄[j₂₆ := __VERIFIER_nondet_int₁][x₇] == a[x₇])
                            && (forall x₈: int, j₆: int ::
                                  (  x₈ == j₆
                                    && 0 <= j₆
                                    && j₆ < j₂₆ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₅: int, j₆: int ::
                                            j₆ < 100000
                                            && x₈ == j₆
                                            && 0 <= j₆
                                            && j₆ < j₂₆ + 1
                                            && b₂₅[j₂₆ := __VERIFIER_nondet_int₂][x₈] == __VERIFIER_nondet_int₂₅)))
                            && (forall x₈: int ::
                                    (exists j₆: int ::
                                            x₈ == j₆
                                            && 0 <= j₆
                                            && j₆ < j₂₆ + 1)
                                    || b₂₅[j₂₆ := __VERIFIER_nondet_int₂][x₈] == b[x₈])
                            && (forall j₆: int ::
                                  (  0 <= j₆
                                    && j₆ < j₂₆ + 1
                                     ==> j₆ < 100000))))
                  &&   j₂₆ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₁₄: int, i₁₃: int ::
                            (  x₁₄ == i₁₃
                              && 0 <= i₁₃
                              && i₁₃ < 0
                               ==> (exists i₁₃: int ::
                                      (a₂₄[i₁₃] == b₂₅[i₁₃]
                                         ==> false))
                                || (exists i₁₃: int ::
                                        a₂₄[i₁₃] == b₂₅[i₁₃]
                                        && i₁₃ < 100000
                                        && x₁₄ == i₁₃
                                        && 0 <= i₁₃
                                        && i₁₃ < 0
                                        && c[x₁₄] == a₂₄[i₁₃])))
                      && (forall x₁₄: int ::
                              (exists i₁₃: int ::
                                      x₁₄ == i₁₃
                                      && 0 <= i₁₃
                                      && i₁₃ < 0)
                              || c[x₁₄] == c[x₁₄])
                      && (forall i₁₃: int ::
                            (  0 <= i₁₃
                              && i₁₃ < 0
                               ==> i₁₃ < 100000))
                      && (forall rv₂₇: int, c₂₈: [int]int, i₂₉: int ::
                            (  0 <= i₂₉
                              && i₂₉ <= 100000
                              && (forall x₁₄: int, i₁₃: int ::
                                    (  x₁₄ == i₁₃
                                      && 0 <= i₁₃
                                      && i₁₃ < i₂₉
                                       ==> (exists i₁₃: int ::
                                              (a₂₄[i₁₃] == b₂₅[i₁₃]
                                                 ==> false))
                                        || (exists i₁₃: int ::
                                                a₂₄[i₁₃] == b₂₅[i₁₃]
                                                && i₁₃ < 100000
                                                && x₁₄ == i₁₃
                                                && 0 <= i₁₃
                                                && i₁₃ < i₂₉
                                                && c₂₈[x₁₄] == a₂₄[i₁₃])))
                              && (forall x₁₄: int ::
                                      (exists i₁₃: int ::
                                              x₁₄ == i₁₃
                                              && 0 <= i₁₃
                                              && i₁₃ < i₂₉)
                                      || c₂₈[x₁₄] == c[x₁₄])
                              && (forall i₁₃: int ::
                                    (  0 <= i₁₃
                                      && i₁₃ < i₂₉
                                       ==> i₁₃ < 100000))
                               ==> (i₂₉ < 100000
                                   ==> a₂₄[i₂₉] == b₂₅[i₂₉]
                                      ||   0 <= i₂₉ + 1
                                        && i₂₉ + 1 <= 100000
                                        && (forall x₁₄: int, i₁₃: int ::
                                              (  x₁₄ == i₁₃
                                                && 0 <= i₁₃
                                                && i₁₃ < i₂₉ + 1
                                                 ==> (exists i₁₃: int ::
                                                        (a₂₄[i₁₃] == b₂₅[i₁₃]
                                                           ==> false))
                                                  || (exists i₁₃: int ::
                                                          a₂₄[i₁₃] == b₂₅[i₁₃]
                                                          && i₁₃ < 100000
                                                          && x₁₄ == i₁₃
                                                          && 0 <= i₁₃
                                                          && i₁₃ < i₂₉ + 1
                                                          && c₂₈[i₂₉ := a₂₄[i₂₉]][x₁₄] == a₂₄[i₁₃])))
                                        && (forall x₁₄: int ::
                                                (exists i₁₃: int ::
                                                        x₁₄ == i₁₃
                                                        && 0 <= i₁₃
                                                        && i₁₃ < i₂₉ + 1)
                                                || c₂₈[i₂₉ := a₂₄[i₂₉]][x₁₄] == c[x₁₄])
                                        && (forall i₁₃: int ::
                                              (  0 <= i₁₃
                                                && i₁₃ < i₂₉ + 1
                                                 ==> i₁₃ < 100000))
                                    && (a₂₄[i₂₉] == b₂₅[i₂₉]
                                       ==> 0 <= i₂₉ + 1
                                        && i₂₉ + 1 <= 100000
                                        && (forall x₁₄: int, i₁₃: int ::
                                              (  x₁₄ == i₁₃
                                                && 0 <= i₁₃
                                                && i₁₃ < i₂₉ + 1
                                                 ==> (exists i₁₃: int ::
                                                        (a₂₄[i₁₃] == b₂₅[i₁₃]
                                                           ==> false))
                                                  || (exists i₁₃: int ::
                                                          a₂₄[i₁₃] == b₂₅[i₁₃]
                                                          && i₁₃ < 100000
                                                          && x₁₄ == i₁₃
                                                          && 0 <= i₁₃
                                                          && i₁₃ < i₂₉ + 1
                                                          && c₂₈[i₂₉ := a₂₄[i₂₉]][x₁₄] == a₂₄[i₁₃])))
                                        && (forall x₁₄: int ::
                                                (exists i₁₃: int ::
                                                        x₁₄ == i₁₃
                                                        && 0 <= i₁₃
                                                        && i₁₃ < i₂₉ + 1)
                                                || c₂₈[i₂₉ := a₂₄[i₂₉]][x₁₄] == c[x₁₄])
                                        && (forall i₁₃: int ::
                                              (  0 <= i₁₃
                                                && i₁₃ < i₂₉ + 1
                                                 ==> i₁₃ < 100000))))
                                &&   i₂₉ < 100000
                                  ||     rv₂₇ == 0
                                      ||   0 <= 0
                                        && 0 <= 100000
                                        && (forall x₁₉: int ::
                                              (  0 <= x₁₉
                                                && x₁₉ < 0
                                                 ==> x₁₉ < 100000))
                                        && (forall x₃₀: int ::
                                              (  0 <= x₃₀
                                                && x₃₀ <= 100000
                                                && (forall x₁₉: int ::
                                                      (  0 <= x₁₉
                                                        && x₁₉ < x₃₀
                                                         ==> x₁₉ < 100000))
                                                 ==> (x₃₀ < 100000
                                                     ==> a₂₄[x₃₀] == b₂₅[x₃₀]
                                                      && 0 <= x₃₀ + 1
                                                      && x₃₀ + 1 <= 100000
                                                      && (forall x₁₉: int ::
                                                            (  0 <= x₁₉
                                                              && x₁₉ < x₃₀ + 1
                                                               ==> x₁₉ < 100000)))
                                                  &&   x₃₀ < 100000
                                                    ||   0 <= 0
                                                      && 0 <= 100000
                                                      && (forall x₂₁: int ::
                                                            (  0 <= x₂₁
                                                              && x₂₁ < 0
                                                               ==> x₂₁ < 100000))
                                                      && (forall x₃₁: int ::
                                                            (  0 <= x₃₁
                                                              && x₃₁ <= 100000
                                                              && (forall x₂₁: int ::
                                                                    (  0 <= x₂₁
                                                                      && x₂₁ < x₃₁
                                                                       ==> x₂₁ < 100000))
                                                               ==> (x₃₁ < 100000
                                                                 ==> a₂₄[x₃₁] == c₂₈[x₃₁]
                                                                  && 0 <= x₃₁ + 1
                                                                  && x₃₁ + 1 <= 100000
                                                                  && (forall x₂₁: int ::
                                                                        (  0 <= x₂₁
                                                                          && x₂₁ < x₃₁ + 1
                                                                           ==> x₂₁ < 100000)))))))
                                    && (rv₂₇ == 0
                                       ==> 0 <= 0
                                        && 0 <= 100000
                                        && (forall x₂₁: int ::
                                              (  0 <= x₂₁
                                                && x₂₁ < 0
                                                 ==> x₂₁ < 100000))
                                        && (forall x₃₄: int ::
                                              (  0 <= x₃₄
                                                && x₃₄ <= 100000
                                                && (forall x₂₁: int ::
                                                      (  0 <= x₂₁
                                                        && x₂₁ < x₃₄
                                                         ==> x₂₁ < 100000))
                                                 ==> (x₃₄ < 100000
                                                   ==> a₂₄[x₃₄] == c₂₈[x₃₄]
                                                    && 0 <= x₃₄ + 1
                                                    && x₃₄ + 1 <= 100000
                                                    && (forall x₂₁: int ::
                                                          (  0 <= x₂₁
                                                            && x₂₁ < x₃₄ + 1
                                                             ==> x₂₁ < 100000)))))))))));


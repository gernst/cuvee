data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, b: [int]int ::
        0 <= 100000
        && (forall x₆: int, i₅: int ::
              (x₆ == i₅
                 ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                          a[i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                          && i₅ < 100000
                          && x₆ == i₅
                          && a[x₆] == __VERIFIER_nondet_int₁₄)
                  || (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                        (a[i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                           ==> false))))
        && (forall x₆: int ::
                (exists i₅: int ::
                      x₆ == i₅)
                || a[x₆] == a[x₆])
        && (forall x₇: int, i₅: int ::
              (x₇ == i₅
                 ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                        a[i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                        && i₅ < 100000
                        && x₇ == i₅
                        && b[x₇] == 20)))
        && (forall x₇: int ::
                (exists i₅: int ::
                      x₇ == i₅)
                || b[x₇] == b[x₇])
        && (forall i₅: int ::
              i₅ < 100000)
        && (forall a₁₃: [int]int, b₁₄: [int]int, i₁₅: int ::
              (  i₁₅ <= 100000
                && (forall x₆: int, i₅: int ::
                      (x₆ == i₅
                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                  a₁₃[i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                                  && i₅ < 100000
                                  && x₆ == i₅
                                  && a₁₃[x₆] == __VERIFIER_nondet_int₁₄)
                          || (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                (a₁₃[i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                                   ==> false))))
                && (forall x₆: int ::
                        (exists i₅: int ::
                              x₆ == i₅)
                        || a₁₃[x₆] == a[x₆])
                && (forall x₇: int, i₅: int ::
                      (x₇ == i₅
                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                a₁₃[i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                                && i₅ < 100000
                                && x₇ == i₅
                                && b₁₄[x₇] == 20)))
                && (forall x₇: int ::
                        (exists i₅: int ::
                              x₇ == i₅)
                        || b₁₄[x₇] == b[x₇])
                && (forall i₅: int ::
                      i₅ < 100000)
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (i₁₅ < 100000
                           ==> (a₁₃[i₁₅ := __VERIFIER_nondet_int₁][i₁₅] == 10
                               ==> i₁₅ + 2 <= 100000
                                && (forall x₆: int, i₅: int ::
                                      (x₆ == i₅
                                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                  a₁₃[i₁₅ := __VERIFIER_nondet_int₁][i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                                                  && i₅ < 100000
                                                  && x₆ == i₅
                                                  && a₁₃[i₁₅ := __VERIFIER_nondet_int₁][x₆] == __VERIFIER_nondet_int₁₄)
                                          || (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                (a₁₃[i₁₅ := __VERIFIER_nondet_int₁][i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                                                   ==> false))))
                                && (forall x₆: int ::
                                        (exists i₅: int ::
                                              x₆ == i₅)
                                        || a₁₃[i₁₅ := __VERIFIER_nondet_int₁][x₆] == a[x₆])
                                && (forall x₇: int, i₅: int ::
                                      (x₇ == i₅
                                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                a₁₃[i₁₅ := __VERIFIER_nondet_int₁][i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                                                && i₅ < 100000
                                                && x₇ == i₅
                                                && b₁₄[i₁₅ := 20][x₇] == 20)))
                                && (forall x₇: int ::
                                        (exists i₅: int ::
                                              x₇ == i₅)
                                        || b₁₄[i₁₅ := 20][x₇] == b[x₇])
                                && (forall i₅: int ::
                                      i₅ < 100000))
                            &&   a₁₃[i₁₅ := __VERIFIER_nondet_int₁][i₁₅] == 10
                              ||   i₁₅ + 2 <= 100000
                                && (forall x₆: int, i₅: int ::
                                      (x₆ == i₅
                                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                  a₁₃[i₁₅ := __VERIFIER_nondet_int₁][i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                                                  && i₅ < 100000
                                                  && x₆ == i₅
                                                  && a₁₃[i₁₅ := __VERIFIER_nondet_int₁][x₆] == __VERIFIER_nondet_int₁₄)
                                          || (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                (a₁₃[i₁₅ := __VERIFIER_nondet_int₁][i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                                                   ==> false))))
                                && (forall x₆: int ::
                                        (exists i₅: int ::
                                              x₆ == i₅)
                                        || a₁₃[i₁₅ := __VERIFIER_nondet_int₁][x₆] == a[x₆])
                                && (forall x₇: int, i₅: int ::
                                      (x₇ == i₅
                                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                                a₁₃[i₁₅ := __VERIFIER_nondet_int₁][i₅ := __VERIFIER_nondet_int₁₄][i₅] == 10
                                                && i₅ < 100000
                                                && x₇ == i₅
                                                && b₁₄[x₇] == 20)))
                                && (forall x₇: int ::
                                        (exists i₅: int ::
                                              x₇ == i₅)
                                        || b₁₄[x₇] == b[x₇])
                                && (forall i₅: int ::
                                      i₅ < 100000)))
                  &&   i₁₅ < 100000
                    ||   0 <= 100000
                      && (forall i₁₁: int ::
                            i₁₁ < 100000)
                      && (forall i₁₆: int ::
                            (  i₁₆ <= 100000
                              && (forall i₁₁: int ::
                                    i₁₁ < 100000)
                               ==> (i₁₆ < 100000
                                 ==> (a₁₃[i₁₆] == 10
                                     ==> b₁₄[i₁₆] == 20
                                      && i₁₆ + 2 <= 100000
                                      && (forall i₁₁: int ::
                                            i₁₁ < 100000))
                                  &&   a₁₃[i₁₆] == 10
                                    ||   i₁₆ + 2 <= 100000
                                      && (forall i₁₁: int ::
                                            i₁₁ < 100000)))))));


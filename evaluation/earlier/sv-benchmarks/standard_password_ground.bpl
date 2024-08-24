data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall password: [int]int, guess: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < 0
                 ==> (exists __VERIFIER_nondet_int₁₄: int, i₆: int ::
                        i₆ < 100000
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < 0
                        && password[x₇] == __VERIFIER_nondet_int₁₄)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < 0)
                || password[x₇] == password[x₇])
        && (forall x₈: int, i₆: int ::
              (  x₈ == i₆
                && 0 <= i₆
                && i₆ < 0
                 ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                        i₆ < 100000
                        && x₈ == i₆
                        && 0 <= i₆
                        && i₆ < 0
                        && guess[x₈] == __VERIFIER_nondet_int₂₅)))
        && (forall x₈: int ::
                (exists i₆: int ::
                        x₈ == i₆
                        && 0 <= i₆
                        && i₆ < 0)
                || guess[x₈] == guess[x₈])
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < 0
                 ==> i₆ < 100000))
        && (forall password₁₉: [int]int, guess₂₀: [int]int, i₂₁: int ::
              (  0 <= i₂₁
                && i₂₁ <= 100000
                && (forall x₇: int, i₆: int ::
                      (  x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₁
                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₆: int ::
                                i₆ < 100000
                                && x₇ == i₆
                                && 0 <= i₆
                                && i₆ < i₂₁
                                && password₁₉[x₇] == __VERIFIER_nondet_int₁₄)))
                && (forall x₇: int ::
                        (exists i₆: int ::
                                x₇ == i₆
                                && 0 <= i₆
                                && i₆ < i₂₁)
                        || password₁₉[x₇] == password[x₇])
                && (forall x₈: int, i₆: int ::
                      (  x₈ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₁
                         ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                                i₆ < 100000
                                && x₈ == i₆
                                && 0 <= i₆
                                && i₆ < i₂₁
                                && guess₂₀[x₈] == __VERIFIER_nondet_int₂₅)))
                && (forall x₈: int ::
                        (exists i₆: int ::
                                x₈ == i₆
                                && 0 <= i₆
                                && i₆ < i₂₁)
                        || guess₂₀[x₈] == guess[x₈])
                && (forall i₆: int ::
                      (  0 <= i₆
                        && i₆ < i₂₁
                         ==> i₆ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
                        (i₂₁ < 100000
                           ==> 0 <= i₂₁ + 1
                            && i₂₁ + 1 <= 100000
                            && (forall x₇: int, i₆: int ::
                                  (  x₇ == i₆
                                    && 0 <= i₆
                                    && i₆ < i₂₁ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₄: int, i₆: int ::
                                            i₆ < 100000
                                            && x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₂₁ + 1
                                            && password₁₉[i₂₁ := __VERIFIER_nondet_int₁][x₇] == __VERIFIER_nondet_int₁₄)))
                            && (forall x₇: int ::
                                    (exists i₆: int ::
                                            x₇ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₂₁ + 1)
                                    || password₁₉[i₂₁ := __VERIFIER_nondet_int₁][x₇] == password[x₇])
                            && (forall x₈: int, i₆: int ::
                                  (  x₈ == i₆
                                    && 0 <= i₆
                                    && i₆ < i₂₁ + 1
                                     ==> (exists __VERIFIER_nondet_int₂₅: int, i₆: int ::
                                            i₆ < 100000
                                            && x₈ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₂₁ + 1
                                            && guess₂₀[i₂₁ := __VERIFIER_nondet_int₂][x₈] == __VERIFIER_nondet_int₂₅)))
                            && (forall x₈: int ::
                                    (exists i₆: int ::
                                            x₈ == i₆
                                            && 0 <= i₆
                                            && i₆ < i₂₁ + 1)
                                    || guess₂₀[i₂₁ := __VERIFIER_nondet_int₂][x₈] == guess[x₈])
                            && (forall i₆: int ::
                                  (  0 <= i₆
                                    && i₆ < i₂₁ + 1
                                     ==> i₆ < 100000))))
                  &&   i₂₁ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall i₁₃: int ::
                            (  0 <= i₁₃
                              && i₁₃ < 0
                               ==> i₁₃ < 100000))
                      && (forall result₂₂: int, i₂₃: int ::
                            (  0 <= i₂₃
                              && i₂₃ <= 100000
                              && (forall i₁₃: int ::
                                    (  0 <= i₁₃
                                      && i₁₃ < i₂₃
                                       ==> i₁₃ < 100000))
                               ==> (i₂₃ < 100000
                                   ==> password₁₉[i₂₃] == guess₂₀[i₂₃]
                                      ||   0 <= i₂₃ + 1
                                        && i₂₃ + 1 <= 100000
                                        && (forall i₁₃: int ::
                                              (  0 <= i₁₃
                                                && i₁₃ < i₂₃ + 1
                                                 ==> i₁₃ < 100000))
                                    && (password₁₉[i₂₃] == guess₂₀[i₂₃]
                                       ==> 0 <= i₂₃ + 1
                                        && i₂₃ + 1 <= 100000
                                        && (forall i₁₃: int ::
                                              (  0 <= i₁₃
                                                && i₁₃ < i₂₃ + 1
                                                 ==> i₁₃ < 100000))))
                                &&   i₂₃ < 100000
                                  || result₂₂ == 0
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₁₇: int ::
                                          (  0 <= x₁₇
                                            && x₁₇ < 0
                                             ==> x₁₇ < 100000))
                                    && (forall x₂₄: int ::
                                          (  0 <= x₂₄
                                            && x₂₄ <= 100000
                                            && (forall x₁₇: int ::
                                                  (  0 <= x₁₇
                                                    && x₁₇ < x₂₄
                                                     ==> x₁₇ < 100000))
                                             ==> (x₂₄ < 100000
                                               ==> password₁₉[x₂₄] == guess₂₀[x₂₄]
                                                && 0 <= x₂₄ + 1
                                                && x₂₄ + 1 <= 100000
                                                && (forall x₁₇: int ::
                                                      (  0 <= x₁₇
                                                        && x₁₇ < x₂₄ + 1
                                                         ==> x₁₇ < 100000))))))))));


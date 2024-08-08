data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int, __VERIFIER_nondet_int₂: int ::
      (forall a: [int]int ::
            (__VERIFIER_nondet_int₂ < 100000
               ==> (  0 < __VERIFIER_nondet_int₁
                && __VERIFIER_nondet_int₁ < 10000
                 ==> 1 <= 1
                  && 1 <= __VERIFIER_nondet_int₂
                  && (forall x₁₀: int, i₉: int ::
                        (  x₁₀ == i₉
                          && 1 <= i₉
                          && i₉ < 1
                           ==> (exists __VERIFIER_nondet_int₃₇: int, i₉: int ::
                                  0 < __VERIFIER_nondet_int₃₇
                                  && __VERIFIER_nondet_int₃₇ < 10000
                                  && i₉ < __VERIFIER_nondet_int₂
                                  && x₁₀ == i₉
                                  && 1 <= i₉
                                  && i₉ < 1
                                  && a[x₁₀] == i₉ + __VERIFIER_nondet_int₁ + __VERIFIER_nondet_int₃₇)))
                  && (forall x₁₀: int ::
                          (exists i₉: int ::
                                  x₁₀ == i₉
                                  && 1 <= i₉
                                  && i₉ < 1)
                          || a[x₁₀] == a[x₁₀])
                  && (forall i₉: int ::
                        (  1 <= i₉
                          && i₉ < 1
                           ==> i₉ < __VERIFIER_nondet_int₂))
                  && (forall a₁₅: [int]int, i₁₆: int ::
                        (  1 <= i₁₆
                          && i₁₆ <= __VERIFIER_nondet_int₂
                          && (forall x₁₀: int, i₉: int ::
                                (  x₁₀ == i₉
                                  && 1 <= i₉
                                  && i₉ < i₁₆
                                   ==> (exists __VERIFIER_nondet_int₃₇: int, i₉: int ::
                                          0 < __VERIFIER_nondet_int₃₇
                                          && __VERIFIER_nondet_int₃₇ < 10000
                                          && i₉ < __VERIFIER_nondet_int₂
                                          && x₁₀ == i₉
                                          && 1 <= i₉
                                          && i₉ < i₁₆
                                          && a₁₅[x₁₀] == i₉ + __VERIFIER_nondet_int₁ + __VERIFIER_nondet_int₃₇)))
                          && (forall x₁₀: int ::
                                  (exists i₉: int ::
                                          x₁₀ == i₉
                                          && 1 <= i₉
                                          && i₉ < i₁₆)
                                  || a₁₅[x₁₀] == a[x₁₀])
                          && (forall i₉: int ::
                                (  1 <= i₉
                                  && i₉ < i₁₆
                                   ==> i₉ < __VERIFIER_nondet_int₂))
                           ==> (forall __VERIFIER_nondet_int₃: int ::
                                  (i₁₆ < __VERIFIER_nondet_int₂
                                     ==> (  0 < __VERIFIER_nondet_int₃
                                      && __VERIFIER_nondet_int₃ < 10000
                                       ==> 1 <= i₁₆ + 1
                                        && i₁₆ + 1 <= __VERIFIER_nondet_int₂
                                        && (forall x₁₀: int, i₉: int ::
                                              (  x₁₀ == i₉
                                                && 1 <= i₉
                                                && i₉ < i₁₆ + 1
                                                 ==> (exists __VERIFIER_nondet_int₃₇: int, i₉: int ::
                                                        0 < __VERIFIER_nondet_int₃₇
                                                        && __VERIFIER_nondet_int₃₇ < 10000
                                                        && i₉ < __VERIFIER_nondet_int₂
                                                        && x₁₀ == i₉
                                                        && 1 <= i₉
                                                        && i₉ < i₁₆ + 1
                                                        && a₁₅[i₁₆ := i₁₆ + __VERIFIER_nondet_int₁ + __VERIFIER_nondet_int₃][x₁₀] == i₉ + __VERIFIER_nondet_int₁ + __VERIFIER_nondet_int₃₇)))
                                        && (forall x₁₀: int ::
                                                (exists i₉: int ::
                                                        x₁₀ == i₉
                                                        && 1 <= i₉
                                                        && i₉ < i₁₆ + 1)
                                                || a₁₅[i₁₆ := i₁₆ + __VERIFIER_nondet_int₁ + __VERIFIER_nondet_int₃][x₁₀] == a[x₁₀])
                                        && (forall i₉: int ::
                                              (  1 <= i₉
                                                && i₉ < i₁₆ + 1
                                                 ==> i₉ < __VERIFIER_nondet_int₂)))))
                            &&   i₁₆ < __VERIFIER_nondet_int₂
                              ||   1 <= 1
                                && 1 <= __VERIFIER_nondet_int₂
                                && (forall i₁₃: int ::
                                      (  1 <= i₁₃
                                        && i₁₃ < 1
                                         ==> i₁₃ < __VERIFIER_nondet_int₂))
                                && (forall i₁₇: int ::
                                      (  1 <= i₁₇
                                        && i₁₇ <= __VERIFIER_nondet_int₂
                                        && (forall i₁₃: int ::
                                              (  1 <= i₁₃
                                                && i₁₃ < i₁₇
                                                 ==> i₁₃ < __VERIFIER_nondet_int₂))
                                         ==> (i₁₇ < __VERIFIER_nondet_int₂
                                           ==> i₁₇ + 2 <= a₁₅[i₁₇]
                                            && 1 <= i₁₇ + 1
                                            && i₁₇ + 1 <= __VERIFIER_nondet_int₂
                                            && (forall i₁₃: int ::
                                                  (  1 <= i₁₃
                                                    && i₁₃ < i₁₇ + 1
                                                     ==> i₁₃ < __VERIFIER_nondet_int₂)))))))))));


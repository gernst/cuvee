data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int ::
        true
        && (  __VERIFIER_nondet_int₁ < 10000
          && -10000 < __VERIFIER_nondet_int₁
           ==> (forall __VERIFIER_nondet_int₂: int ::
                  true
                  && (  __VERIFIER_nondet_int₂ < 10000
                    && -10000 < __VERIFIER_nondet_int₂
                     ==> (forall a: [int]int ::
                          (forall b: [int]int ::
                                  true
                                  && 0 <= 0
                                  && 0 <= __VERIFIER_nondet_int₂
                                  && (forall i₉: int ::
                                        (  i₉ <= i₉
                                          && 0 <= i₉
                                          && i₉ < 0
                                           ==> i₉ < __VERIFIER_nondet_int₂))
                                  && (forall j₂₀: int, i₂₁: int ::
                                        (  true
                                          && 0 <= i₂₁
                                          && i₂₁ <= __VERIFIER_nondet_int₂
                                          && (forall i₉: int ::
                                                (  i₉ <= i₉
                                                  && 0 <= i₉
                                                  && i₉ < i₂₁
                                                   ==> i₉ < __VERIFIER_nondet_int₂))
                                           ==> (i₂₁ < __VERIFIER_nondet_int₂
                                               ==> true
                                                && (  a[i₂₁] < 10000
                                                  && -10000 < a[i₂₁]
                                                   ==> (a[i₂₁] < j₂₀
                                                       ==> true
                                                        && 0 <= i₂₁ + 1
                                                        && i₂₁ + 1 <= __VERIFIER_nondet_int₂
                                                        && (forall i₉: int ::
                                                              (  i₉ <= i₉
                                                                && 0 <= i₉
                                                                && i₉ < i₂₁ + 1
                                                                 ==> i₉ < __VERIFIER_nondet_int₂))
                                                        && true
                                                        && (true
                                                           ==> true))
                                                    && (!(a[i₂₁] < j₂₀
                                                    )
                                                       ==> true
                                                        && 0 <= i₂₁ + 1
                                                        && i₂₁ + 1 <= __VERIFIER_nondet_int₂
                                                        && (forall i₉: int ::
                                                              (  i₉ <= i₉
                                                                && 0 <= i₉
                                                                && i₉ < i₂₁ + 1
                                                                 ==> i₉ < __VERIFIER_nondet_int₂))
                                                        && true
                                                        && (true
                                                           ==> true))))
                                            && (!(i₂₁ < __VERIFIER_nondet_int₂
                                            )
                                               ==> true
                                                && (true
                                                   ==> true
                                                    && 0 <= 0
                                                    && 0 <= __VERIFIER_nondet_int₂
                                                    && (forall x₁₃: int ::
                                                          ((exists i₁₂: int ::
                                                                  x₁₃ == i₁₂
                                                                  && 0 <= i₁₂
                                                                  && i₁₂ < 0)
                                                             ==> (exists i₁₂: int ::
                                                                    i₁₂ < __VERIFIER_nondet_int₂
                                                                    && x₁₃ == i₁₂
                                                                    && 0 <= i₁₂
                                                                    && i₁₂ < 0
                                                                    && b[x₁₃] == a[i₁₂] + -j₂₀)))
                                                    && (forall x₁₃: int ::
                                                          (!((exists i₁₂: int ::
                                                                  x₁₃ == i₁₂
                                                                  && 0 <= i₁₂
                                                                  && i₁₂ < 0)
                                                          )
                                                             ==> b[x₁₃] == b[x₁₃]))
                                                    && (forall i₁₂: int ::
                                                          (  i₁₂ <= i₁₂
                                                            && 0 <= i₁₂
                                                            && i₁₂ < 0
                                                             ==> i₁₂ < __VERIFIER_nondet_int₂))
                                                    && (forall b₂₂: [int]int, i₂₃: int ::
                                                          (  true
                                                            && 0 <= i₂₃
                                                            && i₂₃ <= __VERIFIER_nondet_int₂
                                                            && (forall x₁₃: int ::
                                                                  ((exists i₁₂: int ::
                                                                          x₁₃ == i₁₂
                                                                          && 0 <= i₁₂
                                                                          && i₁₂ < i₂₃)
                                                                     ==> (exists i₁₂: int ::
                                                                            i₁₂ < __VERIFIER_nondet_int₂
                                                                            && x₁₃ == i₁₂
                                                                            && 0 <= i₁₂
                                                                            && i₁₂ < i₂₃
                                                                            && b₂₂[x₁₃] == a[i₁₂] + -j₂₀)))
                                                            && (forall x₁₃: int ::
                                                                  (!((exists i₁₂: int ::
                                                                          x₁₃ == i₁₂
                                                                          && 0 <= i₁₂
                                                                          && i₁₂ < i₂₃)
                                                                  )
                                                                     ==> b₂₂[x₁₃] == b[x₁₃]))
                                                            && (forall i₁₂: int ::
                                                                  (  i₁₂ <= i₁₂
                                                                    && 0 <= i₁₂
                                                                    && i₁₂ < i₂₃
                                                                     ==> i₁₂ < __VERIFIER_nondet_int₂))
                                                             ==> (i₂₃ < __VERIFIER_nondet_int₂
                                                                 ==> true
                                                                  && 0 <= i₂₃ + 1
                                                                  && i₂₃ + 1 <= __VERIFIER_nondet_int₂
                                                                  && (forall x₁₃: int ::
                                                                        ((exists i₁₂: int ::
                                                                                x₁₃ == i₁₂
                                                                                && 0 <= i₁₂
                                                                                && i₁₂ < i₂₃ + 1)
                                                                           ==> (exists i₁₂: int ::
                                                                                  i₁₂ < __VERIFIER_nondet_int₂
                                                                                  && x₁₃ == i₁₂
                                                                                  && 0 <= i₁₂
                                                                                  && i₁₂ < i₂₃ + 1
                                                                                  && b₂₂[i₂₃ := a[i₂₃] - j₂₀][x₁₃] == a[i₁₂] + -j₂₀)))
                                                                  && (forall x₁₃: int ::
                                                                        (!((exists i₁₂: int ::
                                                                                x₁₃ == i₁₂
                                                                                && 0 <= i₁₂
                                                                                && i₁₂ < i₂₃ + 1)
                                                                        )
                                                                           ==> b₂₂[i₂₃ := a[i₂₃] - j₂₀][x₁₃] == b[x₁₃]))
                                                                  && (forall i₁₂: int ::
                                                                        (  i₁₂ <= i₁₂
                                                                          && 0 <= i₁₂
                                                                          && i₁₂ < i₂₃ + 1
                                                                           ==> i₁₂ < __VERIFIER_nondet_int₂))
                                                                  && true
                                                                  && (true
                                                                     ==> true))
                                                              && (!(i₂₃ < __VERIFIER_nondet_int₂
                                                              )
                                                                 ==> true
                                                                  && (true
                                                                     ==> true
                                                                      && 0 <= 0
                                                                      && 0 <= __VERIFIER_nondet_int₂
                                                                      && (forall i₁₇: int ::
                                                                            (  i₁₇ <= i₁₇
                                                                              && 0 <= i₁₇
                                                                              && i₁₇ < 0
                                                                               ==> i₁₇ < __VERIFIER_nondet_int₂))
                                                                      && (forall k₂₄: int, i₂₅: int ::
                                                                            (  true
                                                                              && 0 <= i₂₅
                                                                              && i₂₅ <= __VERIFIER_nondet_int₂
                                                                              && (forall i₁₇: int ::
                                                                                    (  i₁₇ <= i₁₇
                                                                                      && 0 <= i₁₇
                                                                                      && i₁₇ < i₂₅
                                                                                       ==> i₁₇ < __VERIFIER_nondet_int₂))
                                                                               ==> (i₂₅ < __VERIFIER_nondet_int₂
                                                                                   ==> true
                                                                                    && 0 <= i₂₅ + 1
                                                                                    && i₂₅ + 1 <= __VERIFIER_nondet_int₂
                                                                                    && (forall i₁₇: int ::
                                                                                          (  i₁₇ <= i₁₇
                                                                                            && 0 <= i₁₇
                                                                                            && i₁₇ < i₂₅ + 1
                                                                                             ==> i₁₇ < __VERIFIER_nondet_int₂))
                                                                                    && true
                                                                                    && (true
                                                                                       ==> true))
                                                                                && (!(i₂₅ < __VERIFIER_nondet_int₂
                                                                                )
                                                                                   ==> true
                                                                                    && (true
                                                                                       ==> 0 <= k₂₄
                                                                                        && (true
                                                                                           ==> true)))))))))))))))))));


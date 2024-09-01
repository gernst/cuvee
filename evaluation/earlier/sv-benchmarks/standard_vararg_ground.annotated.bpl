data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall aa: [int]int ::
        true
        && 0 <= 0
        && 0 <= 100000
        && (forall x₄: int ::
              ((exists i₃: int ::
                      x₄ == i₃
                      && 0 <= i₃
                      && i₃ < 0)
                 ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                        i₃ < 100000
                        && x₄ == i₃
                        && 0 <= i₃
                        && i₃ < 0
                        && aa[x₄] == __VERIFIER_nondet_int₁₂)))
        && (forall x₄: int ::
              (!((exists i₃: int ::
                      x₄ == i₃
                      && 0 <= i₃
                      && i₃ < 0)
              )
                 ==> aa[x₄] == aa[x₄]))
        && (forall i₃: int ::
              (  i₃ <= i₃
                && 0 <= i₃
                && i₃ < 0
                 ==> i₃ < 100000))
        && (forall aa₁₂: [int]int, i₁₃: int ::
              (  true
                && 0 <= i₁₃
                && i₁₃ <= 100000
                && (forall x₄: int ::
                      ((exists i₃: int ::
                              x₄ == i₃
                              && 0 <= i₃
                              && i₃ < i₁₃)
                         ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                                i₃ < 100000
                                && x₄ == i₃
                                && 0 <= i₃
                                && i₃ < i₁₃
                                && aa₁₂[x₄] == __VERIFIER_nondet_int₁₂)))
                && (forall x₄: int ::
                      (!((exists i₃: int ::
                              x₄ == i₃
                              && 0 <= i₃
                              && i₃ < i₁₃)
                      )
                         ==> aa₁₂[x₄] == aa[x₄]))
                && (forall i₃: int ::
                      (  i₃ <= i₃
                        && 0 <= i₃
                        && i₃ < i₁₃
                         ==> i₃ < 100000))
                 ==> (i₁₃ < 100000
                     ==> (forall __VERIFIER_nondet_int₁: int ::
                            true
                            && 0 <= i₁₃ + 1
                            && i₁₃ + 1 <= 100000
                            && (forall x₄: int ::
                                  ((exists i₃: int ::
                                          x₄ == i₃
                                          && 0 <= i₃
                                          && i₃ < i₁₃ + 1)
                                     ==> (exists __VERIFIER_nondet_int₁₂: int, i₃: int ::
                                            i₃ < 100000
                                            && x₄ == i₃
                                            && 0 <= i₃
                                            && i₃ < i₁₃ + 1
                                            && aa₁₂[i₁₃ := __VERIFIER_nondet_int₁][x₄] == __VERIFIER_nondet_int₁₂)))
                            && (forall x₄: int ::
                                  (!((exists i₃: int ::
                                          x₄ == i₃
                                          && 0 <= i₃
                                          && i₃ < i₁₃ + 1)
                                  )
                                     ==> aa₁₂[i₁₃ := __VERIFIER_nondet_int₁][x₄] == aa[x₄]))
                            && (forall i₃: int ::
                                  (  i₃ <= i₃
                                    && 0 <= i₃
                                    && i₃ < i₁₃ + 1
                                     ==> i₃ < 100000))
                            && true
                            && (true
                               ==> true)))
                  && (!(i₁₃ < 100000
                  )
                     ==> true
                      && (true
                         ==> true
                          && 0 <= 0
                          && 0 <= 1 + aa₁₂[0]
                          && (forall a₇: int ::
                                (  a₇ <= a₇
                                  && 0 <= a₇
                                  && a₇ < 0
                                   ==> 0 <= aa₁₂[a₇]))
                          && (forall a₁₄: int ::
                                (  true
                                  && 0 <= a₁₄
                                  && 0 <= 1 + aa₁₂[a₁₄]
                                  && (forall a₇: int ::
                                        (  a₇ <= a₇
                                          && 0 <= a₇
                                          && a₇ < a₁₄
                                           ==> 0 <= aa₁₂[a₇]))
                                   ==> (0 <= aa₁₂[a₁₄]
                                       ==> true
                                        && 0 <= a₁₄ + 1
                                        && 0 <= 1 + aa₁₂[a₁₄ + 1]
                                        && (forall a₇: int ::
                                              (  a₇ <= a₇
                                                && 0 <= a₇
                                                && a₇ < a₁₄ + 1
                                                 ==> 0 <= aa₁₂[a₇]))
                                        && true
                                        && (true
                                           ==> true))
                                    && (!(0 <= aa₁₂[a₁₄]
                                    )
                                       ==> true
                                        && (true
                                           ==> true
                                            && 0 <= 0
                                            && 0 <= a₁₄
                                            && (forall x₁₀: int ::
                                                  (  x₁₀ <= x₁₀
                                                    && 0 <= x₁₀
                                                    && x₁₀ < 0
                                                     ==> x₁₀ < a₁₄))
                                            && (forall x₁₅: int ::
                                                  (  true
                                                    && 0 <= x₁₅
                                                    && x₁₅ <= a₁₄
                                                    && (forall x₁₀: int ::
                                                          (  x₁₀ <= x₁₀
                                                            && 0 <= x₁₀
                                                            && x₁₀ < x₁₅
                                                             ==> x₁₀ < a₁₄))
                                                     ==> (x₁₅ < a₁₄
                                                         ==> 0 <= aa₁₂[x₁₅]
                                                          && (true
                                                             ==> true
                                                              && 0 <= x₁₅ + 1
                                                              && x₁₅ + 1 <= a₁₄
                                                              && (forall x₁₀: int ::
                                                                    (  x₁₀ <= x₁₀
                                                                      && 0 <= x₁₀
                                                                      && x₁₀ < x₁₅ + 1
                                                                       ==> x₁₀ < a₁₄))
                                                              && true
                                                              && (true
                                                                 ==> true)))
                                                      && (!(x₁₅ < a₁₄
                                                      )
                                                         ==> true
                                                          && (true
                                                             ==> true)))))))))))));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall __VERIFIER_nondet_int₁: int ::
      (1 < __VERIFIER_nondet_int₁
         ==> (forall a: [int]int, acopy: [int]int ::
              (__VERIFIER_nondet_int₁ < 1073741823
                 ==> 0 <= 0
                  && 0 <= __VERIFIER_nondet_int₁
                  && (forall x₇: int, i₆: int ::
                        (  (x₇ == i₆
                             ==> 0 <= i₆
                              && i₆ < 0)
                          &&   x₇ == i₆
                            || x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₆
                           ==> (exists i₆: int ::
                                  i₆ < __VERIFIER_nondet_int₁
                                  && if(x₇ == i₆) then 0 <= i₆ && i₆ < 0 && acopy[x₇] == a[i₆] else x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₆ && acopy[x₇] == a[1 + 2 * __VERIFIER_nondet_int₁ + -i₆])))
                  && (forall x₇: int ::
                          (exists i₆: int ::
                                if(x₇ == i₆) then 0 <= i₆ && i₆ < 0 else x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₆)
                          || acopy[x₇] == acopy[x₇])
                  && (forall i₆: int ::
                        (  0 <= i₆
                          && i₆ < 0
                           ==> i₆ < __VERIFIER_nondet_int₁))
                  && (forall acopy₁₂: [int]int, i₁₃: int ::
                        (  0 <= i₁₃
                          && i₁₃ <= __VERIFIER_nondet_int₁
                          && (forall x₇: int, i₆: int ::
                                (  (x₇ == i₆
                                     ==> 0 <= i₆
                                      && i₆ < i₁₃)
                                  &&   x₇ == i₆
                                    || x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₆
                                   ==> (exists i₆: int ::
                                          i₆ < __VERIFIER_nondet_int₁
                                          && if(x₇ == i₆) then 0 <= i₆ && i₆ < i₁₃ && acopy₁₂[x₇] == a[i₆] else x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₆ && acopy₁₂[x₇] == a[1 + 2 * __VERIFIER_nondet_int₁ + -i₆])))
                          && (forall x₇: int ::
                                  (exists i₆: int ::
                                        if(x₇ == i₆) then 0 <= i₆ && i₆ < i₁₃ else x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₆)
                                  || acopy₁₂[x₇] == acopy[x₇])
                          && (forall i₆: int ::
                                (  0 <= i₆
                                  && i₆ < i₁₃
                                   ==> i₆ < __VERIFIER_nondet_int₁))
                           ==> (i₁₃ < __VERIFIER_nondet_int₁
                               ==> 0 <= i₁₃ + 1
                                && i₁₃ + 1 <= __VERIFIER_nondet_int₁
                                && (forall x₇: int, i₆: int ::
                                      (  (x₇ == i₆
                                           ==> 0 <= i₆
                                            && i₆ < i₁₃ + 1)
                                        &&   x₇ == i₆
                                          || x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₆
                                         ==> (exists i₆: int ::
                                                i₆ < __VERIFIER_nondet_int₁
                                                && if(x₇ == i₆) then 0 <= i₆ && i₆ < i₁₃ + 1 && acopy₁₂[2 * __VERIFIER_nondet_int₁ - i₁₃ + 1 := a[2 * __VERIFIER_nondet_int₁ - i₁₃ + 1]][i₁₃ := a[i₁₃]][x₇] == a[i₆] else x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₆ && acopy₁₂[2 * __VERIFIER_nondet_int₁ - i₁₃ + 1 := a[2 * __VERIFIER_nondet_int₁ - i₁₃ + 1]][i₁₃ := a[i₁₃]][x₇] == a[1 + 2 * __VERIFIER_nondet_int₁ + -i₆])))
                                && (forall x₇: int ::
                                        (exists i₆: int ::
                                              if(x₇ == i₆) then 0 <= i₆ && i₆ < i₁₃ + 1 else x₇ == 1 + 2 * __VERIFIER_nondet_int₁ + -i₆)
                                        || acopy₁₂[2 * __VERIFIER_nondet_int₁ - i₁₃ + 1 := a[2 * __VERIFIER_nondet_int₁ - i₁₃ + 1]][i₁₃ := a[i₁₃]][x₇] == acopy[x₇])
                                && (forall i₆: int ::
                                      (  0 <= i₆
                                        && i₆ < i₁₃ + 1
                                         ==> i₆ < __VERIFIER_nondet_int₁)))
                            &&   i₁₃ < __VERIFIER_nondet_int₁
                              ||   0 <= 0
                                && 0 <= 2 * __VERIFIER_nondet_int₁
                                && (forall i₁₀: int ::
                                      (  0 <= i₁₀
                                        && i₁₀ < 0
                                         ==> i₁₀ < 2 * __VERIFIER_nondet_int₁))
                                && (forall i₁₄: int ::
                                      (  0 <= i₁₄
                                        && i₁₄ <= 2 * __VERIFIER_nondet_int₁
                                        && (forall i₁₀: int ::
                                              (  0 <= i₁₀
                                                && i₁₀ < i₁₄
                                                 ==> i₁₀ < 2 * __VERIFIER_nondet_int₁))
                                         ==> (i₁₄ < 2 * __VERIFIER_nondet_int₁
                                           ==> acopy₁₂[i₁₄] == a[i₁₄]
                                            && 0 <= i₁₄ + 1
                                            && i₁₄ + 1 <= 2 * __VERIFIER_nondet_int₁
                                            && (forall i₁₀: int ::
                                                  (  0 <= i₁₀
                                                    && i₁₀ < i₁₄ + 1
                                                     ==> i₁₀ < 2 * __VERIFIER_nondet_int₁)))))))))));


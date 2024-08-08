data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

var c#heap: c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int ::
        0 <= 0
        && 0 <= 100000
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < 0
                 ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                        i₅ < 100000
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < 0
                        && a[x₆] == __VERIFIER_nondet_int₁₄)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < 0)
                || a[x₆] == a[x₆])
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < 0
                 ==> i₅ < 100000))
        && (forall a₃₉: [int]int, i₄₀: int ::
              (  0 <= i₄₀
                && i₄₀ <= 100000
                && (forall x₆: int, i₅: int ::
                      (  x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₄₀
                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                i₅ < 100000
                                && x₆ == i₅
                                && 0 <= i₅
                                && i₅ < i₄₀
                                && a₃₉[x₆] == __VERIFIER_nondet_int₁₄)))
                && (forall x₆: int ::
                        (exists i₅: int ::
                                x₆ == i₅
                                && 0 <= i₅
                                && i₅ < i₄₀)
                        || a₃₉[x₆] == a[x₆])
                && (forall i₅: int ::
                      (  0 <= i₅
                        && i₅ < i₄₀
                         ==> i₅ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (i₄₀ < 100000
                           ==> 0 <= i₄₀ + 1
                            && i₄₀ + 1 <= 100000
                            && (forall x₆: int, i₅: int ::
                                  (  x₆ == i₅
                                    && 0 <= i₅
                                    && i₅ < i₄₀ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                            i₅ < 100000
                                            && x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₄₀ + 1
                                            && a₃₉[i₄₀ := __VERIFIER_nondet_int₁][x₆] == __VERIFIER_nondet_int₁₄)))
                            && (forall x₆: int ::
                                    (exists i₅: int ::
                                            x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₄₀ + 1)
                                    || a₃₉[i₄₀ := __VERIFIER_nondet_int₁][x₆] == a[x₆])
                            && (forall i₅: int ::
                                  (  0 <= i₅
                                    && i₅ < i₄₀ + 1
                                     ==> i₅ < 100000))))
                  &&   i₄₀ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₂₇: int, s₁₁: int, i₂₅: int ::
                            (  (x₂₇ == i₂₅
                                 ==> 0 <= i₂₅
                                  && i₂₅ < 0)
                              &&   x₂₇ == i₂₅
                                || x₂₇ == s₁₁
                               ==> (exists x₂₂: int, i₂₅: int ::
                                      i₂₅ <= x₂₂
                                      && x₂₂ <= 100000
                                      && (forall x₂₁: int ::
                                            (  i₂₅ <= x₂₁
                                              && x₂₁ < x₂₂
                                               ==> x₂₁ < 100000))
                                      && (x₂₂ < 100000
                                         ==> false))))
                      && (forall x₂₇: int ::
                              (exists s₁₁: int, i₂₅: int ::
                                    if(x₂₇ == i₂₅) then 0 <= i₂₅ && i₂₅ < 0 else x₂₇ == s₁₁)
                              || a₃₉[x₂₇] == a₃₉[x₂₇])
                      && (forall i₂₅: int ::
                            (  0 <= i₂₅
                              && i₂₅ < 0
                               ==> i₂₅ < 100000))
                      && (forall i₄₂: int, a₄₃: [int]int ::
                            (  0 <= i₄₂
                              && i₄₂ <= 100000
                              && (forall x₂₇: int, s₁₁: int, i₂₅: int ::
                                    (  (x₂₇ == i₂₅
                                         ==> 0 <= i₂₅
                                          && i₂₅ < i₄₂)
                                      &&   x₂₇ == i₂₅
                                        || x₂₇ == s₁₁
                                       ==> (exists x₂₂: int, i₂₅: int ::
                                              i₂₅ <= x₂₂
                                              && x₂₂ <= 100000
                                              && (forall x₂₁: int ::
                                                    (  i₂₅ <= x₂₁
                                                      && x₂₁ < x₂₂
                                                       ==> x₂₁ < 100000))
                                              && (x₂₂ < 100000
                                                 ==> false))))
                              && (forall x₂₇: int ::
                                      (exists s₁₁: int, i₂₅: int ::
                                            if(x₂₇ == i₂₅) then 0 <= i₂₅ && i₂₅ < i₄₂ else x₂₇ == s₁₁)
                                      || a₄₃[x₂₇] == a₃₉[x₂₇])
                              && (forall i₂₅: int ::
                                    (  0 <= i₂₅
                                      && i₂₅ < i₄₂
                                       ==> i₂₅ < 100000))
                               ==> (i₄₂ < 100000
                                   ==> 1 + i₄₂ <= i₄₂ + 1
                                    && i₄₂ + 1 <= 100000
                                    && (forall k₁₀: int ::
                                          (  1 + i₄₂ <= k₁₀
                                            && k₁₀ < i₄₂ + 1
                                             ==> k₁₀ < 100000))
                                    && (forall s₅₁: int, k₅₂: int ::
                                          (  1 + i₄₂ <= k₅₂
                                            && k₅₂ <= 100000
                                            && (forall k₁₀: int ::
                                                  (  1 + i₄₂ <= k₁₀
                                                    && k₁₀ < k₅₂
                                                     ==> k₁₀ < 100000))
                                             ==> (k₅₂ < 100000
                                                 ==> (a₄₃[k₅₂] < a₄₃[s₅₁]
                                                     ==> 1 + i₄₂ <= k₅₂ + 1
                                                      && k₅₂ + 1 <= 100000
                                                      && (forall k₁₀: int ::
                                                            (  1 + i₄₂ <= k₁₀
                                                              && k₁₀ < k₅₂ + 1
                                                               ==> k₁₀ < 100000)))
                                                  &&   a₄₃[k₅₂] < a₄₃[s₅₁]
                                                    ||   1 + i₄₂ <= k₅₂ + 1
                                                      && k₅₂ + 1 <= 100000
                                                      && (forall k₁₀: int ::
                                                            (  1 + i₄₂ <= k₁₀
                                                              && k₁₀ < k₅₂ + 1
                                                               ==> k₁₀ < 100000)))
                                              &&   k₅₂ < 100000
                                                ||     s₅₁ == i₄₂
                                                    ||   0 <= 0
                                                      && 0 <= i₄₂
                                                      && (forall x₁₆: int ::
                                                            (  0 <= x₁₆
                                                              && x₁₆ < 0
                                                               ==> x₁₆ < i₄₂))
                                                      && (forall x₅₄: int ::
                                                            (  0 <= x₅₄
                                                              && x₅₄ <= i₄₂
                                                              && (forall x₁₆: int ::
                                                                    (  0 <= x₁₆
                                                                      && x₁₆ < x₅₄
                                                                       ==> x₁₆ < i₄₂))
                                                               ==> (x₅₄ < i₄₂
                                                                   ==> 1 + x₅₄ <= x₅₄ + 1
                                                                    && x₅₄ + 1 <= i₄₂
                                                                    && (forall y₁₃: int ::
                                                                          (  1 + x₅₄ <= y₁₃
                                                                            && y₁₃ < x₅₄ + 1
                                                                             ==> y₁₃ < i₄₂))
                                                                    && (forall y₆₁: int ::
                                                                          (  1 + x₅₄ <= y₆₁
                                                                            && y₆₁ <= i₄₂
                                                                            && (forall y₁₃: int ::
                                                                                  (  1 + x₅₄ <= y₁₃
                                                                                    && y₁₃ < y₆₁
                                                                                     ==> y₁₃ < i₄₂))
                                                                             ==> (y₆₁ < i₄₂
                                                                                 ==> a₄₃[s₅₁ := a₄₃[i₄₂]][i₄₂ := a₄₃[s₅₁]][x₅₄] <= a₄₃[s₅₁ := a₄₃[i₄₂]][i₄₂ := a₄₃[s₅₁]][y₆₁]
                                                                                  && 1 + x₅₄ <= y₆₁ + 1
                                                                                  && y₆₁ + 1 <= i₄₂
                                                                                  && (forall y₁₃: int ::
                                                                                        (  1 + x₅₄ <= y₁₃
                                                                                          && y₁₃ < y₆₁ + 1
                                                                                           ==> y₁₃ < i₄₂)))
                                                                              &&   y₆₁ < i₄₂
                                                                                ||   0 <= x₅₄ + 1
                                                                                  && x₅₄ + 1 <= i₄₂
                                                                                  && (forall x₁₆: int ::
                                                                                        (  0 <= x₁₆
                                                                                          && x₁₆ < x₅₄ + 1
                                                                                           ==> x₁₆ < i₄₂)))))
                                                                &&   x₅₄ < i₄₂
                                                                  ||   i₄₂ <= i₄₂
                                                                    && i₄₂ <= 100000
                                                                    && (forall x₂₁: int ::
                                                                          (  i₄₂ <= x₂₁
                                                                            && x₂₁ < i₄₂
                                                                             ==> x₂₁ < 100000))
                                                                    && (forall x₅₅: int ::
                                                                          (  i₄₂ <= x₅₅
                                                                            && x₅₅ <= 100000
                                                                            && (forall x₂₁: int ::
                                                                                  (  i₄₂ <= x₂₁
                                                                                    && x₂₁ < x₅₅
                                                                                     ==> x₂₁ < 100000))
                                                                             ==> (x₅₅ < 100000
                                                                                 ==> a₄₃[s₅₁ := a₄₃[i₄₂]][i₄₂ := a₄₃[s₅₁]][i₄₂] <= a₄₃[s₅₁ := a₄₃[i₄₂]][i₄₂ := a₄₃[s₅₁]][x₅₅]
                                                                                  && i₄₂ <= x₅₅ + 1
                                                                                  && x₅₅ + 1 <= 100000
                                                                                  && (forall x₂₁: int ::
                                                                                        (  i₄₂ <= x₂₁
                                                                                          && x₂₁ < x₅₅ + 1
                                                                                           ==> x₂₁ < 100000)))
                                                                              &&   x₅₅ < 100000
                                                                                ||   0 <= i₄₂ + 1
                                                                                  && i₄₂ + 1 <= 100000
                                                                                  && (forall x₂₇: int, s₁₁: int, i₂₅: int ::
                                                                                        (  (x₂₇ == i₂₅
                                                                                             ==> 0 <= i₂₅
                                                                                              && i₂₅ < i₄₂ + 1)
                                                                                          &&   x₂₇ == i₂₅
                                                                                            || x₂₇ == s₁₁
                                                                                           ==> (exists x₂₂: int, i₂₅: int ::
                                                                                                  i₂₅ <= x₂₂
                                                                                                  && x₂₂ <= 100000
                                                                                                  && (forall x₂₁: int ::
                                                                                                        (  i₂₅ <= x₂₁
                                                                                                          && x₂₁ < x₂₂
                                                                                                           ==> x₂₁ < 100000))
                                                                                                  && (x₂₂ < 100000
                                                                                                     ==> false))))
                                                                                  && (forall x₂₇: int ::
                                                                                          (exists s₁₁: int, i₂₅: int ::
                                                                                                if(x₂₇ == i₂₅) then 0 <= i₂₅ && i₂₅ < i₄₂ + 1 else x₂₇ == s₁₁)
                                                                                          || a₄₃[s₅₁ := a₄₃[i₄₂]][i₄₂ := a₄₃[s₅₁]][x₂₇] == a₃₉[x₂₇])
                                                                                  && (forall i₂₅: int ::
                                                                                        (  0 <= i₂₅
                                                                                          && i₂₅ < i₄₂ + 1
                                                                                           ==> i₂₅ < 100000))))))
                                                  && (s₅₁ == i₄₂
                                                     ==> 0 <= 0
                                                      && 0 <= i₄₂
                                                      && (forall x₁₆: int ::
                                                            (  0 <= x₁₆
                                                              && x₁₆ < 0
                                                               ==> x₁₆ < i₄₂))
                                                      && (forall x₆₆: int ::
                                                            (  0 <= x₆₆
                                                              && x₆₆ <= i₄₂
                                                              && (forall x₁₆: int ::
                                                                    (  0 <= x₁₆
                                                                      && x₁₆ < x₆₆
                                                                       ==> x₁₆ < i₄₂))
                                                               ==> (x₆₆ < i₄₂
                                                                   ==> 1 + x₆₆ <= x₆₆ + 1
                                                                    && x₆₆ + 1 <= i₄₂
                                                                    && (forall y₁₃: int ::
                                                                          (  1 + x₆₆ <= y₁₃
                                                                            && y₁₃ < x₆₆ + 1
                                                                             ==> y₁₃ < i₄₂))
                                                                    && (forall y₇₃: int ::
                                                                          (  1 + x₆₆ <= y₇₃
                                                                            && y₇₃ <= i₄₂
                                                                            && (forall y₁₃: int ::
                                                                                  (  1 + x₆₆ <= y₁₃
                                                                                    && y₁₃ < y₇₃
                                                                                     ==> y₁₃ < i₄₂))
                                                                             ==> (y₇₃ < i₄₂
                                                                                 ==> a₄₃[x₆₆] <= a₄₃[y₇₃]
                                                                                  && 1 + x₆₆ <= y₇₃ + 1
                                                                                  && y₇₃ + 1 <= i₄₂
                                                                                  && (forall y₁₃: int ::
                                                                                        (  1 + x₆₆ <= y₁₃
                                                                                          && y₁₃ < y₇₃ + 1
                                                                                           ==> y₁₃ < i₄₂)))
                                                                              &&   y₇₃ < i₄₂
                                                                                ||   0 <= x₆₆ + 1
                                                                                  && x₆₆ + 1 <= i₄₂
                                                                                  && (forall x₁₆: int ::
                                                                                        (  0 <= x₁₆
                                                                                          && x₁₆ < x₆₆ + 1
                                                                                           ==> x₁₆ < i₄₂)))))
                                                                &&   x₆₆ < i₄₂
                                                                  ||   i₄₂ <= i₄₂
                                                                    && i₄₂ <= 100000
                                                                    && (forall x₂₁: int ::
                                                                          (  i₄₂ <= x₂₁
                                                                            && x₂₁ < i₄₂
                                                                             ==> x₂₁ < 100000))
                                                                    && (forall x₆₇: int ::
                                                                          (  i₄₂ <= x₆₇
                                                                            && x₆₇ <= 100000
                                                                            && (forall x₂₁: int ::
                                                                                  (  i₄₂ <= x₂₁
                                                                                    && x₂₁ < x₆₇
                                                                                     ==> x₂₁ < 100000))
                                                                             ==> (x₆₇ < 100000
                                                                                 ==> a₄₃[i₄₂] <= a₄₃[x₆₇]
                                                                                  && i₄₂ <= x₆₇ + 1
                                                                                  && x₆₇ + 1 <= 100000
                                                                                  && (forall x₂₁: int ::
                                                                                        (  i₄₂ <= x₂₁
                                                                                          && x₂₁ < x₆₇ + 1
                                                                                           ==> x₂₁ < 100000)))
                                                                              &&   x₆₇ < 100000
                                                                                ||   0 <= i₄₂ + 1
                                                                                  && i₄₂ + 1 <= 100000
                                                                                  && (forall x₂₇: int, s₁₁: int, i₂₅: int ::
                                                                                        (  (x₂₇ == i₂₅
                                                                                             ==> 0 <= i₂₅
                                                                                              && i₂₅ < i₄₂ + 1)
                                                                                          &&   x₂₇ == i₂₅
                                                                                            || x₂₇ == s₁₁
                                                                                           ==> (exists x₂₂: int, i₂₅: int ::
                                                                                                  i₂₅ <= x₂₂
                                                                                                  && x₂₂ <= 100000
                                                                                                  && (forall x₂₁: int ::
                                                                                                        (  i₂₅ <= x₂₁
                                                                                                          && x₂₁ < x₂₂
                                                                                                           ==> x₂₁ < 100000))
                                                                                                  && (x₂₂ < 100000
                                                                                                     ==> false))))
                                                                                  && (forall x₂₇: int ::
                                                                                          (exists s₁₁: int, i₂₅: int ::
                                                                                                if(x₂₇ == i₂₅) then 0 <= i₂₅ && i₂₅ < i₄₂ + 1 else x₂₇ == s₁₁)
                                                                                          || a₄₃[x₂₇] == a₃₉[x₂₇])
                                                                                  && (forall i₂₅: int ::
                                                                                        (  0 <= i₂₅
                                                                                          && i₂₅ < i₄₂ + 1
                                                                                           ==> i₂₅ < 100000))))))))))
                                &&   i₄₂ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₃₅: int ::
                                          (  0 <= x₃₅
                                            && x₃₅ < 0
                                             ==> x₃₅ < 100000))
                                    && (forall x₄₆: int ::
                                          (  0 <= x₄₆
                                            && x₄₆ <= 100000
                                            && (forall x₃₅: int ::
                                                  (  0 <= x₃₅
                                                    && x₃₅ < x₄₆
                                                     ==> x₃₅ < 100000))
                                             ==> (x₄₆ < 100000
                                               ==> 1 + x₄₆ <= x₄₆ + 1
                                                && x₄₆ + 1 <= 100000
                                                && (forall y₃₂: int ::
                                                      (  1 + x₄₆ <= y₃₂
                                                        && y₃₂ < x₄₆ + 1
                                                         ==> y₃₂ < 100000))
                                                && (forall y₄₇: int ::
                                                      (  1 + x₄₆ <= y₄₇
                                                        && y₄₇ <= 100000
                                                        && (forall y₃₂: int ::
                                                              (  1 + x₄₆ <= y₃₂
                                                                && y₃₂ < y₄₇
                                                                 ==> y₃₂ < 100000))
                                                         ==> (y₄₇ < 100000
                                                             ==> a₄₃[x₄₆] <= a₄₃[y₄₇]
                                                              && 1 + x₄₆ <= y₄₇ + 1
                                                              && y₄₇ + 1 <= 100000
                                                              && (forall y₃₂: int ::
                                                                    (  1 + x₄₆ <= y₃₂
                                                                      && y₃₂ < y₄₇ + 1
                                                                       ==> y₃₂ < 100000)))
                                                          &&   y₄₇ < 100000
                                                            ||   0 <= x₄₆ + 1
                                                              && x₄₆ + 1 <= 100000
                                                              && (forall x₃₅: int ::
                                                                    (  0 <= x₃₅
                                                                      && x₃₅ < x₄₆ + 1
                                                                       ==> x₃₅ < 100000))))))))))));


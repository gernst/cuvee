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
        && (forall a₃₈: [int]int, i₃₉: int ::
              (  0 <= i₃₉
                && i₃₉ <= 100000
                && (forall x₆: int, i₅: int ::
                      (  x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₃₉
                         ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                i₅ < 100000
                                && x₆ == i₅
                                && 0 <= i₅
                                && i₅ < i₃₉
                                && a₃₈[x₆] == __VERIFIER_nondet_int₁₄)))
                && (forall x₆: int ::
                        (exists i₅: int ::
                                x₆ == i₅
                                && 0 <= i₅
                                && i₅ < i₃₉)
                        || a₃₈[x₆] == a[x₆])
                && (forall i₅: int ::
                      (  0 <= i₅
                        && i₅ < i₃₉
                         ==> i₅ < 100000))
                 ==> (forall __VERIFIER_nondet_int₁: int ::
                        (i₃₉ < 100000
                           ==> 0 <= i₃₉ + 1
                            && i₃₉ + 1 <= 100000
                            && (forall x₆: int, i₅: int ::
                                  (  x₆ == i₅
                                    && 0 <= i₅
                                    && i₅ < i₃₉ + 1
                                     ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                                            i₅ < 100000
                                            && x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₃₉ + 1
                                            && a₃₈[i₃₉ := __VERIFIER_nondet_int₁][x₆] == __VERIFIER_nondet_int₁₄)))
                            && (forall x₆: int ::
                                    (exists i₅: int ::
                                            x₆ == i₅
                                            && 0 <= i₅
                                            && i₅ < i₃₉ + 1)
                                    || a₃₈[i₃₉ := __VERIFIER_nondet_int₁][x₆] == a[x₆])
                            && (forall i₅: int ::
                                  (  0 <= i₅
                                    && i₅ < i₃₉ + 1
                                     ==> i₅ < 100000))))
                  &&   i₃₉ < 100000
                    ||   0 <= 0
                      && 0 <= 100000
                      && (forall x₂₇: int, s₁₁: int, i₂₅: int ::
                            (  (x₂₇ == i₂₅
                                 ==> 0 <= i₂₅
                                  && i₂₅ < 0)
                              &&   x₂₇ == i₂₅
                                || x₂₇ == s₁₁
                               ==> (exists x₂₂: int, i₂₅: int ::
                                      1 + i₂₅ <= x₂₂
                                      && x₂₂ <= 100000
                                      && (forall x₂₁: int ::
                                            (  1 + i₂₅ <= x₂₁
                                              && x₂₁ < x₂₂
                                               ==> x₂₁ < 100000))
                                      && (x₂₂ < 100000
                                         ==> false))))
                      && (forall x₂₇: int ::
                              (exists s₁₁: int, i₂₅: int ::
                                    if(x₂₇ == i₂₅) then 0 <= i₂₅ && i₂₅ < 0 else x₂₇ == s₁₁)
                              || a₃₈[x₂₇] == a₃₈[x₂₇])
                      && (forall i₂₅: int ::
                            (  0 <= i₂₅
                              && i₂₅ < 0
                               ==> i₂₅ < 100000))
                      && (forall i₄₁: int, a₄₂: [int]int ::
                            (  0 <= i₄₁
                              && i₄₁ <= 100000
                              && (forall x₂₇: int, s₁₁: int, i₂₅: int ::
                                    (  (x₂₇ == i₂₅
                                         ==> 0 <= i₂₅
                                          && i₂₅ < i₄₁)
                                      &&   x₂₇ == i₂₅
                                        || x₂₇ == s₁₁
                                       ==> (exists x₂₂: int, i₂₅: int ::
                                              1 + i₂₅ <= x₂₂
                                              && x₂₂ <= 100000
                                              && (forall x₂₁: int ::
                                                    (  1 + i₂₅ <= x₂₁
                                                      && x₂₁ < x₂₂
                                                       ==> x₂₁ < 100000))
                                              && (x₂₂ < 100000
                                                 ==> false))))
                              && (forall x₂₇: int ::
                                      (exists s₁₁: int, i₂₅: int ::
                                            if(x₂₇ == i₂₅) then 0 <= i₂₅ && i₂₅ < i₄₁ else x₂₇ == s₁₁)
                                      || a₄₂[x₂₇] == a₃₈[x₂₇])
                              && (forall i₂₅: int ::
                                    (  0 <= i₂₅
                                      && i₂₅ < i₄₁
                                       ==> i₂₅ < 100000))
                               ==> (i₄₁ < 100000
                                   ==> i₄₁ <= i₄₁
                                    && i₄₁ <= 100000
                                    && (forall k₁₀: int ::
                                          (  i₄₁ <= k₁₀
                                            && k₁₀ < i₄₁
                                             ==> k₁₀ < 100000))
                                    && (forall s₅₀: int, k₅₁: int ::
                                          (  i₄₁ <= k₅₁
                                            && k₅₁ <= 100000
                                            && (forall k₁₀: int ::
                                                  (  i₄₁ <= k₁₀
                                                    && k₁₀ < k₅₁
                                                     ==> k₁₀ < 100000))
                                             ==> (k₅₁ < 100000
                                                 ==> (a₄₂[s₅₀] < a₄₂[k₅₁]
                                                     ==> i₄₁ <= k₅₁ + 1
                                                      && k₅₁ + 1 <= 100000
                                                      && (forall k₁₀: int ::
                                                            (  i₄₁ <= k₁₀
                                                              && k₁₀ < k₅₁ + 1
                                                               ==> k₁₀ < 100000)))
                                                  &&   a₄₂[s₅₀] < a₄₂[k₅₁]
                                                    ||   i₄₁ <= k₅₁ + 1
                                                      && k₅₁ + 1 <= 100000
                                                      && (forall k₁₀: int ::
                                                            (  i₄₁ <= k₁₀
                                                              && k₁₀ < k₅₁ + 1
                                                               ==> k₁₀ < 100000)))
                                              &&   k₅₁ < 100000
                                                ||     s₅₀ == i₄₁
                                                    ||   0 <= 0
                                                      && 0 <= i₄₁
                                                      && (forall x₁₆: int ::
                                                            (  0 <= x₁₆
                                                              && x₁₆ < 0
                                                               ==> x₁₆ < i₄₁))
                                                      && (forall x₅₃: int ::
                                                            (  0 <= x₅₃
                                                              && x₅₃ <= i₄₁
                                                              && (forall x₁₆: int ::
                                                                    (  0 <= x₁₆
                                                                      && x₁₆ < x₅₃
                                                                       ==> x₁₆ < i₄₁))
                                                               ==> (x₅₃ < i₄₁
                                                                   ==> 1 + x₅₃ <= x₅₃ + 1
                                                                    && x₅₃ + 1 <= i₄₁
                                                                    && (forall y₁₃: int ::
                                                                          (  1 + x₅₃ <= y₁₃
                                                                            && y₁₃ < x₅₃ + 1
                                                                             ==> y₁₃ < i₄₁))
                                                                    && (forall y₆₀: int ::
                                                                          (  1 + x₅₃ <= y₆₀
                                                                            && y₆₀ <= i₄₁
                                                                            && (forall y₁₃: int ::
                                                                                  (  1 + x₅₃ <= y₁₃
                                                                                    && y₁₃ < y₆₀
                                                                                     ==> y₁₃ < i₄₁))
                                                                             ==> (y₆₀ < i₄₁
                                                                                 ==> a₄₂[s₅₀ := a₄₂[i₄₁]][i₄₁ := a₄₂[s₅₀]][x₅₃] <= a₄₂[s₅₀ := a₄₂[i₄₁]][i₄₁ := a₄₂[s₅₀]][y₆₀]
                                                                                  && 1 + x₅₃ <= y₆₀ + 1
                                                                                  && y₆₀ + 1 <= i₄₁
                                                                                  && (forall y₁₃: int ::
                                                                                        (  1 + x₅₃ <= y₁₃
                                                                                          && y₁₃ < y₆₀ + 1
                                                                                           ==> y₁₃ < i₄₁)))
                                                                              &&   y₆₀ < i₄₁
                                                                                ||   0 <= x₅₃ + 1
                                                                                  && x₅₃ + 1 <= i₄₁
                                                                                  && (forall x₁₆: int ::
                                                                                        (  0 <= x₁₆
                                                                                          && x₁₆ < x₅₃ + 1
                                                                                           ==> x₁₆ < i₄₁)))))
                                                                &&   x₅₃ < i₄₁
                                                                  ||   1 + i₄₁ <= i₄₁ + 1
                                                                    && i₄₁ + 1 <= 100000
                                                                    && (forall x₂₁: int ::
                                                                          (  1 + i₄₁ <= x₂₁
                                                                            && x₂₁ < i₄₁ + 1
                                                                             ==> x₂₁ < 100000))
                                                                    && (forall x₅₄: int ::
                                                                          (  1 + i₄₁ <= x₅₄
                                                                            && x₅₄ <= 100000
                                                                            && (forall x₂₁: int ::
                                                                                  (  1 + i₄₁ <= x₂₁
                                                                                    && x₂₁ < x₅₄
                                                                                     ==> x₂₁ < 100000))
                                                                             ==> (x₅₄ < 100000
                                                                                 ==> a₄₂[s₅₀ := a₄₂[i₄₁]][i₄₁ := a₄₂[s₅₀]][i₄₁] <= a₄₂[s₅₀ := a₄₂[i₄₁]][i₄₁ := a₄₂[s₅₀]][x₅₄]
                                                                                  && 1 + i₄₁ <= x₅₄ + 1
                                                                                  && x₅₄ + 1 <= 100000
                                                                                  && (forall x₂₁: int ::
                                                                                        (  1 + i₄₁ <= x₂₁
                                                                                          && x₂₁ < x₅₄ + 1
                                                                                           ==> x₂₁ < 100000)))
                                                                              &&   x₅₄ < 100000
                                                                                ||   0 <= i₄₁ + 1
                                                                                  && i₄₁ + 1 <= 100000
                                                                                  && (forall x₂₇: int, s₁₁: int, i₂₅: int ::
                                                                                        (  (x₂₇ == i₂₅
                                                                                             ==> 0 <= i₂₅
                                                                                              && i₂₅ < i₄₁ + 1)
                                                                                          &&   x₂₇ == i₂₅
                                                                                            || x₂₇ == s₁₁
                                                                                           ==> (exists x₂₂: int, i₂₅: int ::
                                                                                                  1 + i₂₅ <= x₂₂
                                                                                                  && x₂₂ <= 100000
                                                                                                  && (forall x₂₁: int ::
                                                                                                        (  1 + i₂₅ <= x₂₁
                                                                                                          && x₂₁ < x₂₂
                                                                                                           ==> x₂₁ < 100000))
                                                                                                  && (x₂₂ < 100000
                                                                                                     ==> false))))
                                                                                  && (forall x₂₇: int ::
                                                                                          (exists s₁₁: int, i₂₅: int ::
                                                                                                if(x₂₇ == i₂₅) then 0 <= i₂₅ && i₂₅ < i₄₁ + 1 else x₂₇ == s₁₁)
                                                                                          || a₄₂[s₅₀ := a₄₂[i₄₁]][i₄₁ := a₄₂[s₅₀]][x₂₇] == a₃₈[x₂₇])
                                                                                  && (forall i₂₅: int ::
                                                                                        (  0 <= i₂₅
                                                                                          && i₂₅ < i₄₁ + 1
                                                                                           ==> i₂₅ < 100000))))))
                                                  && (s₅₀ == i₄₁
                                                     ==> 0 <= 0
                                                      && 0 <= i₄₁
                                                      && (forall x₁₆: int ::
                                                            (  0 <= x₁₆
                                                              && x₁₆ < 0
                                                               ==> x₁₆ < i₄₁))
                                                      && (forall x₆₅: int ::
                                                            (  0 <= x₆₅
                                                              && x₆₅ <= i₄₁
                                                              && (forall x₁₆: int ::
                                                                    (  0 <= x₁₆
                                                                      && x₁₆ < x₆₅
                                                                       ==> x₁₆ < i₄₁))
                                                               ==> (x₆₅ < i₄₁
                                                                   ==> 1 + x₆₅ <= x₆₅ + 1
                                                                    && x₆₅ + 1 <= i₄₁
                                                                    && (forall y₁₃: int ::
                                                                          (  1 + x₆₅ <= y₁₃
                                                                            && y₁₃ < x₆₅ + 1
                                                                             ==> y₁₃ < i₄₁))
                                                                    && (forall y₇₂: int ::
                                                                          (  1 + x₆₅ <= y₇₂
                                                                            && y₇₂ <= i₄₁
                                                                            && (forall y₁₃: int ::
                                                                                  (  1 + x₆₅ <= y₁₃
                                                                                    && y₁₃ < y₇₂
                                                                                     ==> y₁₃ < i₄₁))
                                                                             ==> (y₇₂ < i₄₁
                                                                                 ==> a₄₂[x₆₅] <= a₄₂[y₇₂]
                                                                                  && 1 + x₆₅ <= y₇₂ + 1
                                                                                  && y₇₂ + 1 <= i₄₁
                                                                                  && (forall y₁₃: int ::
                                                                                        (  1 + x₆₅ <= y₁₃
                                                                                          && y₁₃ < y₇₂ + 1
                                                                                           ==> y₁₃ < i₄₁)))
                                                                              &&   y₇₂ < i₄₁
                                                                                ||   0 <= x₆₅ + 1
                                                                                  && x₆₅ + 1 <= i₄₁
                                                                                  && (forall x₁₆: int ::
                                                                                        (  0 <= x₁₆
                                                                                          && x₁₆ < x₆₅ + 1
                                                                                           ==> x₁₆ < i₄₁)))))
                                                                &&   x₆₅ < i₄₁
                                                                  ||   1 + i₄₁ <= i₄₁ + 1
                                                                    && i₄₁ + 1 <= 100000
                                                                    && (forall x₂₁: int ::
                                                                          (  1 + i₄₁ <= x₂₁
                                                                            && x₂₁ < i₄₁ + 1
                                                                             ==> x₂₁ < 100000))
                                                                    && (forall x₆₆: int ::
                                                                          (  1 + i₄₁ <= x₆₆
                                                                            && x₆₆ <= 100000
                                                                            && (forall x₂₁: int ::
                                                                                  (  1 + i₄₁ <= x₂₁
                                                                                    && x₂₁ < x₆₆
                                                                                     ==> x₂₁ < 100000))
                                                                             ==> (x₆₆ < 100000
                                                                                 ==> a₄₂[i₄₁] <= a₄₂[x₆₆]
                                                                                  && 1 + i₄₁ <= x₆₆ + 1
                                                                                  && x₆₆ + 1 <= 100000
                                                                                  && (forall x₂₁: int ::
                                                                                        (  1 + i₄₁ <= x₂₁
                                                                                          && x₂₁ < x₆₆ + 1
                                                                                           ==> x₂₁ < 100000)))
                                                                              &&   x₆₆ < 100000
                                                                                ||   0 <= i₄₁ + 1
                                                                                  && i₄₁ + 1 <= 100000
                                                                                  && (forall x₂₇: int, s₁₁: int, i₂₅: int ::
                                                                                        (  (x₂₇ == i₂₅
                                                                                             ==> 0 <= i₂₅
                                                                                              && i₂₅ < i₄₁ + 1)
                                                                                          &&   x₂₇ == i₂₅
                                                                                            || x₂₇ == s₁₁
                                                                                           ==> (exists x₂₂: int, i₂₅: int ::
                                                                                                  1 + i₂₅ <= x₂₂
                                                                                                  && x₂₂ <= 100000
                                                                                                  && (forall x₂₁: int ::
                                                                                                        (  1 + i₂₅ <= x₂₁
                                                                                                          && x₂₁ < x₂₂
                                                                                                           ==> x₂₁ < 100000))
                                                                                                  && (x₂₂ < 100000
                                                                                                     ==> false))))
                                                                                  && (forall x₂₇: int ::
                                                                                          (exists s₁₁: int, i₂₅: int ::
                                                                                                if(x₂₇ == i₂₅) then 0 <= i₂₅ && i₂₅ < i₄₁ + 1 else x₂₇ == s₁₁)
                                                                                          || a₄₂[x₂₇] == a₃₈[x₂₇])
                                                                                  && (forall i₂₅: int ::
                                                                                        (  0 <= i₂₅
                                                                                          && i₂₅ < i₄₁ + 1
                                                                                           ==> i₂₅ < 100000))))))))))
                                &&   i₄₁ < 100000
                                  ||   0 <= 0
                                    && 0 <= 100000
                                    && (forall x₃₅: int ::
                                          (  0 <= x₃₅
                                            && x₃₅ < 0
                                             ==> x₃₅ < 100000))
                                    && (forall x₄₅: int ::
                                          (  0 <= x₄₅
                                            && x₄₅ <= 100000
                                            && (forall x₃₅: int ::
                                                  (  0 <= x₃₅
                                                    && x₃₅ < x₄₅
                                                     ==> x₃₅ < 100000))
                                             ==> (x₄₅ < 100000
                                               ==> 1 + x₄₅ <= x₄₅ + 1
                                                && x₄₅ + 1 <= 100000
                                                && (forall y₃₂: int ::
                                                      (  1 + x₄₅ <= y₃₂
                                                        && y₃₂ < x₄₅ + 1
                                                         ==> y₃₂ < 100000))
                                                && (forall y₄₆: int ::
                                                      (  1 + x₄₅ <= y₄₆
                                                        && y₄₆ <= 100000
                                                        && (forall y₃₂: int ::
                                                              (  1 + x₄₅ <= y₃₂
                                                                && y₃₂ < y₄₆
                                                                 ==> y₃₂ < 100000))
                                                         ==> (y₄₆ < 100000
                                                             ==> a₄₂[x₄₅] <= a₄₂[y₄₆]
                                                              && 1 + x₄₅ <= y₄₆ + 1
                                                              && y₄₆ + 1 <= 100000
                                                              && (forall y₃₂: int ::
                                                                    (  1 + x₄₅ <= y₃₂
                                                                      && y₃₂ < y₄₆ + 1
                                                                       ==> y₃₂ < 100000)))
                                                          &&   y₄₆ < 100000
                                                            ||   0 <= x₄₅ + 1
                                                              && x₄₅ + 1 <= 100000
                                                              && (forall x₃₅: int ::
                                                                    (  0 <= x₃₅
                                                                      && x₃₅ < x₄₅ + 1
                                                                       ==> x₃₅ < 100000))))))))))));


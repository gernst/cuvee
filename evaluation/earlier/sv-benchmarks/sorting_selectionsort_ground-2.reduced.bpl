data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, s₄₉: int, k₅₀: int, x₅₂: int, y₅₉: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₄₀
                 ==> (exists s₁₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₂₄ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₂₄ <= x₂₀
                                  && x₂₀ < x₂₁
                                   ==> x₂₀ < 100000))
                          && (x₂₁ < 100000
                             ==> false)
                          && 0 <= x₁₇
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₇
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₂₄))
                                          && (y₁₃ < i₂₄
                                             ==> false)
                                          && x₁₅ < i₂₄)))
                          && (x₁₇ < i₂₄
                             ==> false)
                          && (s₁₀ == i₂₄
                             ==> false)
                          && 1 + i₂₄ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₂₄ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₂₄ < 100000
                          && a₄₁[i₂₄] == a₃₇[s₁₀]
                          &&   s₁₀ == i₂₄
                            || a₄₁[s₁₀] == a₃₇[i₂₄])
                  || (exists s₁₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₂₄ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₂₄ <= x₂₀
                                  && x₂₀ < x₂₂
                                   ==> x₂₀ < 100000))
                          && (x₂₂ < 100000
                             ==> false)
                          && 0 <= x₁₉
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₉
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₂₄))
                                          && (y₁₃ < i₂₄
                                             ==> false)
                                          && x₁₅ < i₂₄)))
                          && (x₁₉ < i₂₄
                             ==> false)
                          && s₁₀ == i₂₄
                          && 1 + i₂₄ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₂₄ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₂₄ < 100000)))
        && (forall i₂₄: int, s₁₀: int ::
                  0 <= i₂₄
                  && i₂₄ < i₄₀
                ||   a₄₁[i₂₄] == a₃₇[i₂₄]
                  && a₄₁[s₁₀] == a₃₇[s₁₀])
        && i₄₀ < 100000
        && i₄₀ + 1 <= k₅₀
        && (forall s₈: int, k₉: int ::
              (  i₄₀ + 1 <= k₉
                && k₉ < k₅₀
                 ==> a₄₁[k₉] < a₄₁[s₈]
                    && k₉ < 100000
                  ||   (a₄₁[k₉] < a₄₁[s₈]
                       ==> false)
                    && k₉ < 100000))
        && 0 <= x₅₂
        && (forall x₁₅: int ::
              (  0 <= x₁₅
                && x₁₅ < x₅₂
                 ==> (exists y₁₃: int ::
                        1 + x₁₅ <= y₁₃
                        && (forall y₁₂: int ::
                              (  1 + x₁₅ <= y₁₂
                                && y₁₂ < y₁₃
                                 ==> y₁₂ < i₄₀))
                        && (y₁₃ < i₄₀
                           ==> false)
                        && x₁₅ < i₄₀)))
        && x₅₂ < i₄₀
        && x₅₂ + 1 <= y₅₉
        && (forall y₁₂: int ::
              (  x₅₂ + 1 <= y₁₂
                && y₁₂ < y₅₉
                 ==> y₁₂ < i₄₀))
        && y₅₉ < i₄₀
         ==> s₄₉ == i₄₀
          || k₅₀ < 100000
          || i₃₈ < 100000
          || a₄₁[s₄₉ := a₄₁[i₄₀]][i₄₀ := a₄₁[s₄₉]][x₅₂] <= a₄₁[s₄₉ := a₄₁[i₄₀]][i₄₀ := a₄₁[s₄₉]][y₅₉]));

goal {:named "assert"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, s₄₉: int, k₅₀: int, x₅₂: int, x₅₃: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₄₀
                 ==> (exists s₁₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₂₄ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₂₄ <= x₂₀
                                  && x₂₀ < x₂₁
                                   ==> x₂₀ < 100000))
                          && (x₂₁ < 100000
                             ==> false)
                          && 0 <= x₁₇
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₇
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₂₄))
                                          && (y₁₃ < i₂₄
                                             ==> false)
                                          && x₁₅ < i₂₄)))
                          && (x₁₇ < i₂₄
                             ==> false)
                          && (s₁₀ == i₂₄
                             ==> false)
                          && 1 + i₂₄ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₂₄ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₂₄ < 100000
                          && a₄₁[i₂₄] == a₃₇[s₁₀]
                          &&   s₁₀ == i₂₄
                            || a₄₁[s₁₀] == a₃₇[i₂₄])
                  || (exists s₁₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₂₄ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₂₄ <= x₂₀
                                  && x₂₀ < x₂₂
                                   ==> x₂₀ < 100000))
                          && (x₂₂ < 100000
                             ==> false)
                          && 0 <= x₁₉
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₉
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₂₄))
                                          && (y₁₃ < i₂₄
                                             ==> false)
                                          && x₁₅ < i₂₄)))
                          && (x₁₉ < i₂₄
                             ==> false)
                          && s₁₀ == i₂₄
                          && 1 + i₂₄ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₂₄ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₂₄ < 100000)))
        && (forall i₂₄: int, s₁₀: int ::
                  0 <= i₂₄
                  && i₂₄ < i₄₀
                ||   a₄₁[i₂₄] == a₃₇[i₂₄]
                  && a₄₁[s₁₀] == a₃₇[s₁₀])
        && i₄₀ < 100000
        && i₄₀ + 1 <= k₅₀
        && (forall s₈: int, k₉: int ::
              (  i₄₀ + 1 <= k₉
                && k₉ < k₅₀
                 ==> a₄₁[k₉] < a₄₁[s₈]
                    && k₉ < 100000
                  ||   (a₄₁[k₉] < a₄₁[s₈]
                       ==> false)
                    && k₉ < 100000))
        && 0 <= x₅₂
        && (forall x₁₅: int ::
              (  0 <= x₁₅
                && x₁₅ < x₅₂
                 ==> (exists y₁₃: int ::
                        1 + x₁₅ <= y₁₃
                        && (forall y₁₂: int ::
                              (  1 + x₁₅ <= y₁₂
                                && y₁₂ < y₁₃
                                 ==> y₁₂ < i₄₀))
                        && (y₁₃ < i₄₀
                           ==> false)
                        && x₁₅ < i₄₀)))
        && i₄₀ <= x₅₃
        && (forall x₂₀: int ::
              (  i₄₀ <= x₂₀
                && x₂₀ < x₅₃
                 ==> x₂₀ < 100000))
        && x₅₃ < 100000
         ==> x₅₂ < i₄₀
          || s₄₉ == i₄₀
          || k₅₀ < 100000
          || i₃₈ < 100000
          || a₄₁[s₄₉ := a₄₁[i₄₀]][i₄₀ := a₄₁[s₄₉]][i₄₀] <= a₄₁[s₄₉ := a₄₁[i₄₀]][i₄₀ := a₄₁[s₄₉]][x₅₃]));

goal {:named "invariant forward"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, s₄₉: int, k₅₀: int, x₅₂: int, x₅₃: int, i₂₄: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₃₂₇: int ::
              (  0 <= i₃₂₇
                && i₃₂₇ < i₄₀
                 ==> (exists s₁₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₃₂₇ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₃₂₇ <= x₂₀
                                  && x₂₀ < x₂₁
                                   ==> x₂₀ < 100000))
                          && (x₂₁ < 100000
                             ==> false)
                          && 0 <= x₁₇
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₇
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₃₂₇))
                                          && (y₁₃ < i₃₂₇
                                             ==> false)
                                          && x₁₅ < i₃₂₇)))
                          && (x₁₇ < i₃₂₇
                             ==> false)
                          && (s₁₀ == i₃₂₇
                             ==> false)
                          && 1 + i₃₂₇ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₂₇ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₂₇ < 100000
                          && a₄₁[i₃₂₇] == a₃₇[s₁₀]
                          &&   s₁₀ == i₃₂₇
                            || a₄₁[s₁₀] == a₃₇[i₃₂₇])
                  || (exists s₁₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₃₂₇ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₃₂₇ <= x₂₀
                                  && x₂₀ < x₂₂
                                   ==> x₂₀ < 100000))
                          && (x₂₂ < 100000
                             ==> false)
                          && 0 <= x₁₉
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₉
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₃₂₇))
                                          && (y₁₃ < i₃₂₇
                                             ==> false)
                                          && x₁₅ < i₃₂₇)))
                          && (x₁₉ < i₃₂₇
                             ==> false)
                          && s₁₀ == i₃₂₇
                          && 1 + i₃₂₇ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₂₇ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₂₇ < 100000)))
        && (forall i₃₂₈: int, s₁₀: int ::
                  0 <= i₃₂₈
                  && i₃₂₈ < i₄₀
                ||   a₄₁[i₃₂₈] == a₃₇[i₃₂₈]
                  && a₄₁[s₁₀] == a₃₇[s₁₀])
        && i₄₀ < 100000
        && i₄₀ + 1 <= k₅₀
        && (forall s₈: int, k₉: int ::
              (  i₄₀ + 1 <= k₉
                && k₉ < k₅₀
                 ==> a₄₁[k₉] < a₄₁[s₈]
                    && k₉ < 100000
                  ||   (a₄₁[k₉] < a₄₁[s₈]
                       ==> false)
                    && k₉ < 100000))
        && 0 <= x₅₂
        && (forall x₁₅: int ::
              (  0 <= x₁₅
                && x₁₅ < x₅₂
                 ==> (exists y₁₃: int ::
                        1 + x₁₅ <= y₁₃
                        && (forall y₁₂: int ::
                              (  1 + x₁₅ <= y₁₂
                                && y₁₂ < y₁₃
                                 ==> y₁₂ < i₄₀))
                        && (y₁₃ < i₄₀
                           ==> false)
                        && x₁₅ < i₄₀)))
        && i₄₀ <= x₅₃
        && (forall x₂₀: int ::
              (  i₄₀ <= x₂₀
                && x₂₀ < x₅₃
                 ==> x₂₀ < 100000))
         ==> 0 <= i₂₄
          || x₅₃ < 100000
          || x₅₂ < i₄₀
          || s₄₉ == i₄₀
          || k₅₀ < 100000
          || i₃₈ < 100000
          || a₄₁[s₄₉ := a₄₁[i₄₀]][i₄₀ := a₄₁[s₄₉]][i₂₄] == a₃₇[i₂₄]));

goal {:named "invariant forward"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, s₄₉: int, k₅₀: int, x₅₂: int, x₅₃: int, i₂₄: int, s₁₀: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₃₄₀: int ::
              (  0 <= i₃₄₀
                && i₃₄₀ < i₄₀
                 ==> (exists s₃₄₁: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₃₄₀ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₃₄₀ <= x₂₀
                                  && x₂₀ < x₂₁
                                   ==> x₂₀ < 100000))
                          && (x₂₁ < 100000
                             ==> false)
                          && 0 <= x₁₇
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₇
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₃₄₀))
                                          && (y₁₃ < i₃₄₀
                                             ==> false)
                                          && x₁₅ < i₃₄₀)))
                          && (x₁₇ < i₃₄₀
                             ==> false)
                          && (s₃₄₁ == i₃₄₀
                             ==> false)
                          && 1 + i₃₄₀ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₄₀ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₄₀ < 100000
                          && a₄₁[i₃₄₀] == a₃₇[s₃₄₁]
                          &&   s₃₄₁ == i₃₄₀
                            || a₄₁[s₃₄₁] == a₃₇[i₃₄₀])
                  || (exists s₃₄₂: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₃₄₀ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₃₄₀ <= x₂₀
                                  && x₂₀ < x₂₂
                                   ==> x₂₀ < 100000))
                          && (x₂₂ < 100000
                             ==> false)
                          && 0 <= x₁₉
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₉
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₃₄₀))
                                          && (y₁₃ < i₃₄₀
                                             ==> false)
                                          && x₁₅ < i₃₄₀)))
                          && (x₁₉ < i₃₄₀
                             ==> false)
                          && s₃₄₂ == i₃₄₀
                          && 1 + i₃₄₀ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₄₀ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₄₀ < 100000)))
        && (forall i₃₄₃: int, s₃₄₄: int ::
                  0 <= i₃₄₃
                  && i₃₄₃ < i₄₀
                ||   a₄₁[i₃₄₃] == a₃₇[i₃₄₃]
                  && a₄₁[s₃₄₄] == a₃₇[s₃₄₄])
        && i₄₀ < 100000
        && i₄₀ + 1 <= k₅₀
        && (forall s₈: int, k₉: int ::
              (  i₄₀ + 1 <= k₉
                && k₉ < k₅₀
                 ==> a₄₁[k₉] < a₄₁[s₈]
                    && k₉ < 100000
                  ||   (a₄₁[k₉] < a₄₁[s₈]
                       ==> false)
                    && k₉ < 100000))
        && 0 <= x₅₂
        && (forall x₁₅: int ::
              (  0 <= x₁₅
                && x₁₅ < x₅₂
                 ==> (exists y₁₃: int ::
                        1 + x₁₅ <= y₁₃
                        && (forall y₁₂: int ::
                              (  1 + x₁₅ <= y₁₂
                                && y₁₂ < y₁₃
                                 ==> y₁₂ < i₄₀))
                        && (y₁₃ < i₄₀
                           ==> false)
                        && x₁₅ < i₄₀)))
        && i₄₀ <= x₅₃
        && (forall x₂₀: int ::
              (  i₄₀ <= x₂₀
                && x₂₀ < x₅₃
                 ==> x₂₀ < 100000))
         ==> 0 <= i₂₄
          || x₅₃ < 100000
          || x₅₂ < i₄₀
          || s₄₉ == i₄₀
          || k₅₀ < 100000
          || i₃₈ < 100000
          || a₄₁[s₄₉ := a₄₁[i₄₀]][i₄₀ := a₄₁[s₄₉]][s₁₀] == a₃₇[s₁₀]));

goal {:named "invariant forward"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, s₄₉: int, k₅₀: int, x₅₂: int, x₅₃: int, i₂₄: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₃₅₅: int ::
              (  0 <= i₃₅₅
                && i₃₅₅ < i₄₀
                 ==> (exists s₁₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₃₅₅ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₃₅₅ <= x₂₀
                                  && x₂₀ < x₂₁
                                   ==> x₂₀ < 100000))
                          && (x₂₁ < 100000
                             ==> false)
                          && 0 <= x₁₇
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₇
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₃₅₅))
                                          && (y₁₃ < i₃₅₅
                                             ==> false)
                                          && x₁₅ < i₃₅₅)))
                          && (x₁₇ < i₃₅₅
                             ==> false)
                          && (s₁₀ == i₃₅₅
                             ==> false)
                          && 1 + i₃₅₅ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₅₅ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₅₅ < 100000
                          && a₄₁[i₃₅₅] == a₃₇[s₁₀]
                          &&   s₁₀ == i₃₅₅
                            || a₄₁[s₁₀] == a₃₇[i₃₅₅])
                  || (exists s₁₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₃₅₅ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₃₅₅ <= x₂₀
                                  && x₂₀ < x₂₂
                                   ==> x₂₀ < 100000))
                          && (x₂₂ < 100000
                             ==> false)
                          && 0 <= x₁₉
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₉
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₃₅₅))
                                          && (y₁₃ < i₃₅₅
                                             ==> false)
                                          && x₁₅ < i₃₅₅)))
                          && (x₁₉ < i₃₅₅
                             ==> false)
                          && s₁₀ == i₃₅₅
                          && 1 + i₃₅₅ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₅₅ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₅₅ < 100000)))
        && (forall i₃₅₆: int, s₁₀: int ::
                  0 <= i₃₅₆
                  && i₃₅₆ < i₄₀
                ||   a₄₁[i₃₅₆] == a₃₇[i₃₅₆]
                  && a₄₁[s₁₀] == a₃₇[s₁₀])
        && i₄₀ < 100000
        && i₄₀ + 1 <= k₅₀
        && (forall s₈: int, k₉: int ::
              (  i₄₀ + 1 <= k₉
                && k₉ < k₅₀
                 ==> a₄₁[k₉] < a₄₁[s₈]
                    && k₉ < 100000
                  ||   (a₄₁[k₉] < a₄₁[s₈]
                       ==> false)
                    && k₉ < 100000))
        && 0 <= x₅₂
        && (forall x₁₅: int ::
              (  0 <= x₁₅
                && x₁₅ < x₅₂
                 ==> (exists y₁₃: int ::
                        1 + x₁₅ <= y₁₃
                        && (forall y₁₂: int ::
                              (  1 + x₁₅ <= y₁₂
                                && y₁₂ < y₁₃
                                 ==> y₁₂ < i₄₀))
                        && (y₁₃ < i₄₀
                           ==> false)
                        && x₁₅ < i₄₀)))
        && i₄₀ <= x₅₃
        && (forall x₂₀: int ::
              (  i₄₀ <= x₂₀
                && x₂₀ < x₅₃
                 ==> x₂₀ < 100000))
         ==> i₂₄ < i₄₀ + 1
          || x₅₃ < 100000
          || x₅₂ < i₄₀
          || s₄₉ == i₄₀
          || k₅₀ < 100000
          || i₃₈ < 100000
          || a₄₁[s₄₉ := a₄₁[i₄₀]][i₄₀ := a₄₁[s₄₉]][i₂₄] == a₃₇[i₂₄]));

goal {:named "invariant forward"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, s₄₉: int, k₅₀: int, x₅₂: int, x₅₃: int, i₂₄: int, s₁₀: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₃₆₈: int ::
              (  0 <= i₃₆₈
                && i₃₆₈ < i₄₀
                 ==> (exists s₃₆₉: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₃₆₈ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₃₆₈ <= x₂₀
                                  && x₂₀ < x₂₁
                                   ==> x₂₀ < 100000))
                          && (x₂₁ < 100000
                             ==> false)
                          && 0 <= x₁₇
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₇
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₃₆₈))
                                          && (y₁₃ < i₃₆₈
                                             ==> false)
                                          && x₁₅ < i₃₆₈)))
                          && (x₁₇ < i₃₆₈
                             ==> false)
                          && (s₃₆₉ == i₃₆₈
                             ==> false)
                          && 1 + i₃₆₈ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₆₈ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₆₈ < 100000
                          && a₄₁[i₃₆₈] == a₃₇[s₃₆₉]
                          &&   s₃₆₉ == i₃₆₈
                            || a₄₁[s₃₆₉] == a₃₇[i₃₆₈])
                  || (exists s₃₇₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₃₆₈ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₃₆₈ <= x₂₀
                                  && x₂₀ < x₂₂
                                   ==> x₂₀ < 100000))
                          && (x₂₂ < 100000
                             ==> false)
                          && 0 <= x₁₉
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₉
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₃₆₈))
                                          && (y₁₃ < i₃₆₈
                                             ==> false)
                                          && x₁₅ < i₃₆₈)))
                          && (x₁₉ < i₃₆₈
                             ==> false)
                          && s₃₇₀ == i₃₆₈
                          && 1 + i₃₆₈ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₆₈ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₆₈ < 100000)))
        && (forall i₃₇₁: int, s₃₇₂: int ::
                  0 <= i₃₇₁
                  && i₃₇₁ < i₄₀
                ||   a₄₁[i₃₇₁] == a₃₇[i₃₇₁]
                  && a₄₁[s₃₇₂] == a₃₇[s₃₇₂])
        && i₄₀ < 100000
        && i₄₀ + 1 <= k₅₀
        && (forall s₈: int, k₉: int ::
              (  i₄₀ + 1 <= k₉
                && k₉ < k₅₀
                 ==> a₄₁[k₉] < a₄₁[s₈]
                    && k₉ < 100000
                  ||   (a₄₁[k₉] < a₄₁[s₈]
                       ==> false)
                    && k₉ < 100000))
        && 0 <= x₅₂
        && (forall x₁₅: int ::
              (  0 <= x₁₅
                && x₁₅ < x₅₂
                 ==> (exists y₁₃: int ::
                        1 + x₁₅ <= y₁₃
                        && (forall y₁₂: int ::
                              (  1 + x₁₅ <= y₁₂
                                && y₁₂ < y₁₃
                                 ==> y₁₂ < i₄₀))
                        && (y₁₃ < i₄₀
                           ==> false)
                        && x₁₅ < i₄₀)))
        && i₄₀ <= x₅₃
        && (forall x₂₀: int ::
              (  i₄₀ <= x₂₀
                && x₂₀ < x₅₃
                 ==> x₂₀ < 100000))
         ==> i₂₄ < i₄₀ + 1
          || x₅₃ < 100000
          || x₅₂ < i₄₀
          || s₄₉ == i₄₀
          || k₅₀ < 100000
          || i₃₈ < 100000
          || a₄₁[s₄₉ := a₄₁[i₄₀]][i₄₀ := a₄₁[s₄₉]][s₁₀] == a₃₇[s₁₀]));

goal {:named "assert"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, s₄₉: int, k₅₀: int, x₆₄: int, y₇₁: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₄₀
                 ==> (exists s₁₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₂₄ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₂₄ <= x₂₀
                                  && x₂₀ < x₂₁
                                   ==> x₂₀ < 100000))
                          && (x₂₁ < 100000
                             ==> false)
                          && 0 <= x₁₇
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₇
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₂₄))
                                          && (y₁₃ < i₂₄
                                             ==> false)
                                          && x₁₅ < i₂₄)))
                          && (x₁₇ < i₂₄
                             ==> false)
                          && (s₁₀ == i₂₄
                             ==> false)
                          && 1 + i₂₄ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₂₄ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₂₄ < 100000
                          && a₄₁[i₂₄] == a₃₇[s₁₀]
                          &&   s₁₀ == i₂₄
                            || a₄₁[s₁₀] == a₃₇[i₂₄])
                  || (exists s₁₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₂₄ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₂₄ <= x₂₀
                                  && x₂₀ < x₂₂
                                   ==> x₂₀ < 100000))
                          && (x₂₂ < 100000
                             ==> false)
                          && 0 <= x₁₉
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₉
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₂₄))
                                          && (y₁₃ < i₂₄
                                             ==> false)
                                          && x₁₅ < i₂₄)))
                          && (x₁₉ < i₂₄
                             ==> false)
                          && s₁₀ == i₂₄
                          && 1 + i₂₄ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₂₄ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₂₄ < 100000)))
        && (forall i₂₄: int, s₁₀: int ::
                  0 <= i₂₄
                  && i₂₄ < i₄₀
                ||   a₄₁[i₂₄] == a₃₇[i₂₄]
                  && a₄₁[s₁₀] == a₃₇[s₁₀])
        && i₄₀ < 100000
        && i₄₀ + 1 <= k₅₀
        && (forall s₈: int, k₉: int ::
              (  i₄₀ + 1 <= k₉
                && k₉ < k₅₀
                 ==> a₄₁[k₉] < a₄₁[s₈]
                    && k₉ < 100000
                  ||   (a₄₁[k₉] < a₄₁[s₈]
                       ==> false)
                    && k₉ < 100000))
        && s₄₉ == i₄₀
        && 0 <= x₆₄
        && (forall x₁₅: int ::
              (  0 <= x₁₅
                && x₁₅ < x₆₄
                 ==> (exists y₁₃: int ::
                        1 + x₁₅ <= y₁₃
                        && (forall y₁₂: int ::
                              (  1 + x₁₅ <= y₁₂
                                && y₁₂ < y₁₃
                                 ==> y₁₂ < i₄₀))
                        && (y₁₃ < i₄₀
                           ==> false)
                        && x₁₅ < i₄₀)))
        && x₆₄ < i₄₀
        && x₆₄ + 1 <= y₇₁
        && (forall y₁₂: int ::
              (  x₆₄ + 1 <= y₁₂
                && y₁₂ < y₇₁
                 ==> y₁₂ < i₄₀))
        && y₇₁ < i₄₀
         ==> k₅₀ < 100000
          || i₃₈ < 100000
          || a₄₁[x₆₄] <= a₄₁[y₇₁]));

goal {:named "assert"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, s₄₉: int, k₅₀: int, x₆₄: int, x₆₅: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₄₀
                 ==> (exists s₁₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₂₄ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₂₄ <= x₂₀
                                  && x₂₀ < x₂₁
                                   ==> x₂₀ < 100000))
                          && (x₂₁ < 100000
                             ==> false)
                          && 0 <= x₁₇
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₇
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₂₄))
                                          && (y₁₃ < i₂₄
                                             ==> false)
                                          && x₁₅ < i₂₄)))
                          && (x₁₇ < i₂₄
                             ==> false)
                          && (s₁₀ == i₂₄
                             ==> false)
                          && 1 + i₂₄ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₂₄ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₂₄ < 100000
                          && a₄₁[i₂₄] == a₃₇[s₁₀]
                          &&   s₁₀ == i₂₄
                            || a₄₁[s₁₀] == a₃₇[i₂₄])
                  || (exists s₁₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₂₄ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₂₄ <= x₂₀
                                  && x₂₀ < x₂₂
                                   ==> x₂₀ < 100000))
                          && (x₂₂ < 100000
                             ==> false)
                          && 0 <= x₁₉
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₉
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₂₄))
                                          && (y₁₃ < i₂₄
                                             ==> false)
                                          && x₁₅ < i₂₄)))
                          && (x₁₉ < i₂₄
                             ==> false)
                          && s₁₀ == i₂₄
                          && 1 + i₂₄ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₂₄ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₂₄ < 100000)))
        && (forall i₂₄: int, s₁₀: int ::
                  0 <= i₂₄
                  && i₂₄ < i₄₀
                ||   a₄₁[i₂₄] == a₃₇[i₂₄]
                  && a₄₁[s₁₀] == a₃₇[s₁₀])
        && i₄₀ < 100000
        && i₄₀ + 1 <= k₅₀
        && (forall s₈: int, k₉: int ::
              (  i₄₀ + 1 <= k₉
                && k₉ < k₅₀
                 ==> a₄₁[k₉] < a₄₁[s₈]
                    && k₉ < 100000
                  ||   (a₄₁[k₉] < a₄₁[s₈]
                       ==> false)
                    && k₉ < 100000))
        && s₄₉ == i₄₀
        && 0 <= x₆₄
        && (forall x₁₅: int ::
              (  0 <= x₁₅
                && x₁₅ < x₆₄
                 ==> (exists y₁₃: int ::
                        1 + x₁₅ <= y₁₃
                        && (forall y₁₂: int ::
                              (  1 + x₁₅ <= y₁₂
                                && y₁₂ < y₁₃
                                 ==> y₁₂ < i₄₀))
                        && (y₁₃ < i₄₀
                           ==> false)
                        && x₁₅ < i₄₀)))
        && i₄₀ <= x₆₅
        && (forall x₂₀: int ::
              (  i₄₀ <= x₂₀
                && x₂₀ < x₆₅
                 ==> x₂₀ < 100000))
        && x₆₅ < 100000
         ==> x₆₄ < i₄₀
          || k₅₀ < 100000
          || i₃₈ < 100000
          || a₄₁[i₄₀] <= a₄₁[x₆₅]));

goal {:named "invariant forward"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, s₄₉: int, k₅₀: int, x₆₄: int, x₆₅: int, i₂₄: int, s₁₀: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₅₅₈: int ::
              (  0 <= i₅₅₈
                && i₅₅₈ < i₄₀
                 ==> (exists s₅₅₉: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₅₅₈ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₅₅₈ <= x₂₀
                                  && x₂₀ < x₂₁
                                   ==> x₂₀ < 100000))
                          && (x₂₁ < 100000
                             ==> false)
                          && 0 <= x₁₇
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₇
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₅₅₈))
                                          && (y₁₃ < i₅₅₈
                                             ==> false)
                                          && x₁₅ < i₅₅₈)))
                          && (x₁₇ < i₅₅₈
                             ==> false)
                          && (s₅₅₉ == i₅₅₈
                             ==> false)
                          && 1 + i₅₅₈ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₅₅₈ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₅₅₈ < 100000
                          && a₄₁[i₅₅₈] == a₃₇[s₅₅₉]
                          &&   s₅₅₉ == i₅₅₈
                            || a₄₁[s₅₅₉] == a₃₇[i₅₅₈])
                  || (exists s₅₆₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₅₅₈ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₅₅₈ <= x₂₀
                                  && x₂₀ < x₂₂
                                   ==> x₂₀ < 100000))
                          && (x₂₂ < 100000
                             ==> false)
                          && 0 <= x₁₉
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₉
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₅₅₈))
                                          && (y₁₃ < i₅₅₈
                                             ==> false)
                                          && x₁₅ < i₅₅₈)))
                          && (x₁₉ < i₅₅₈
                             ==> false)
                          && s₅₆₀ == i₅₅₈
                          && 1 + i₅₅₈ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₅₅₈ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₅₅₈ < 100000)))
        && (forall i₅₆₁: int, s₅₆₂: int ::
                  0 <= i₅₆₁
                  && i₅₆₁ < i₄₀
                ||   a₄₁[i₅₆₁] == a₃₇[i₅₆₁]
                  && a₄₁[s₅₆₂] == a₃₇[s₅₆₂])
        && i₄₀ < 100000
        && i₄₀ + 1 <= k₅₀
        && (forall s₈: int, k₉: int ::
              (  i₄₀ + 1 <= k₉
                && k₉ < k₅₀
                 ==> a₄₁[k₉] < a₄₁[s₈]
                    && k₉ < 100000
                  ||   (a₄₁[k₉] < a₄₁[s₈]
                       ==> false)
                    && k₉ < 100000))
        && s₄₉ == i₄₀
        && 0 <= x₆₄
        && (forall x₁₅: int ::
              (  0 <= x₁₅
                && x₁₅ < x₆₄
                 ==> (exists y₁₃: int ::
                        1 + x₁₅ <= y₁₃
                        && (forall y₁₂: int ::
                              (  1 + x₁₅ <= y₁₂
                                && y₁₂ < y₁₃
                                 ==> y₁₂ < i₄₀))
                        && (y₁₃ < i₄₀
                           ==> false)
                        && x₁₅ < i₄₀)))
        && i₄₀ <= x₆₅
        && (forall x₂₀: int ::
              (  i₄₀ <= x₂₀
                && x₂₀ < x₆₅
                 ==> x₂₀ < 100000))
         ==> i₂₄ < i₄₀ + 1
          || x₆₅ < 100000
          || x₆₄ < i₄₀
          || k₅₀ < 100000
          || i₃₈ < 100000
          || a₄₁[s₁₀] == a₃₇[s₁₀]));

goal {:named "assert"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, x₄₄: int, y₄₅: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₄₀
                 ==> (exists s₁₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₂₄ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₂₄ <= x₂₀
                                  && x₂₀ < x₂₁
                                   ==> x₂₀ < 100000))
                          && (x₂₁ < 100000
                             ==> false)
                          && 0 <= x₁₇
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₇
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₂₄))
                                          && (y₁₃ < i₂₄
                                             ==> false)
                                          && x₁₅ < i₂₄)))
                          && (x₁₇ < i₂₄
                             ==> false)
                          && (s₁₀ == i₂₄
                             ==> false)
                          && 1 + i₂₄ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₂₄ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₂₄ < 100000
                          && a₄₁[i₂₄] == a₃₇[s₁₀]
                          &&   s₁₀ == i₂₄
                            || a₄₁[s₁₀] == a₃₇[i₂₄])
                  || (exists s₁₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₂₄ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₂₄ <= x₂₀
                                  && x₂₀ < x₂₂
                                   ==> x₂₀ < 100000))
                          && (x₂₂ < 100000
                             ==> false)
                          && 0 <= x₁₉
                          && (forall x₁₅: int ::
                                (  0 <= x₁₅
                                  && x₁₅ < x₁₉
                                   ==> (exists y₁₃: int ::
                                          1 + x₁₅ <= y₁₃
                                          && (forall y₁₂: int ::
                                                (  1 + x₁₅ <= y₁₂
                                                  && y₁₂ < y₁₃
                                                   ==> y₁₂ < i₂₄))
                                          && (y₁₃ < i₂₄
                                             ==> false)
                                          && x₁₅ < i₂₄)))
                          && (x₁₉ < i₂₄
                             ==> false)
                          && s₁₀ == i₂₄
                          && 1 + i₂₄ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₂₄ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₂₄ < 100000)))
        && (forall i₂₄: int, s₁₀: int ::
                  0 <= i₂₄
                  && i₂₄ < i₄₀
                ||   a₄₁[i₂₄] == a₃₇[i₂₄]
                  && a₄₁[s₁₀] == a₃₇[s₁₀])
        && 0 <= x₄₄
        && (forall x₃₃: int ::
              (  0 <= x₃₃
                && x₃₃ < x₄₄
                 ==> (exists y₃₁: int ::
                        1 + x₃₃ <= y₃₁
                        && (forall y₃₀: int ::
                              (  1 + x₃₃ <= y₃₀
                                && y₃₀ < y₃₁
                                 ==> y₃₀ < 100000))
                        && (y₃₁ < 100000
                           ==> false)
                        && x₃₃ < 100000)))
        && x₄₄ < 100000
        && x₄₄ + 1 <= y₄₅
        && (forall y₃₀: int ::
              (  x₄₄ + 1 <= y₃₀
                && y₃₀ < y₄₅
                 ==> y₃₀ < 100000))
        && y₄₅ < 100000
         ==> i₄₀ < 100000
          || i₃₈ < 100000
          || a₄₁[x₄₄] <= a₄₁[y₄₅]));


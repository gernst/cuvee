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
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
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
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
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
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₃₂₈: int ::
              (  0 <= i₃₂₈
                && i₃₂₈ < i₄₀
                 ==> (exists s₁₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₃₂₈ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₃₂₈ <= x₂₀
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
                                                   ==> y₁₂ < i₃₂₈))
                                          && (y₁₃ < i₃₂₈
                                             ==> false)
                                          && x₁₅ < i₃₂₈)))
                          && (x₁₇ < i₃₂₈
                             ==> false)
                          && (s₁₀ == i₃₂₈
                             ==> false)
                          && 1 + i₃₂₈ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₂₈ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₂₈ < 100000
                          && a₄₁[i₃₂₈] == a₃₇[s₁₀]
                          &&   s₁₀ == i₃₂₈
                            || a₄₁[s₁₀] == a₃₇[i₃₂₈])
                  || (exists s₁₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₃₂₈ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₃₂₈ <= x₂₀
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
                                                   ==> y₁₂ < i₃₂₈))
                                          && (y₁₃ < i₃₂₈
                                             ==> false)
                                          && x₁₅ < i₃₂₈)))
                          && (x₁₉ < i₃₂₈
                             ==> false)
                          && s₁₀ == i₃₂₈
                          && 1 + i₃₂₈ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₂₈ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₂₈ < 100000)))
        && (forall i₃₂₉: int, s₁₀: int ::
                  0 <= i₃₂₉
                  && i₃₂₉ < i₄₀
                ||   a₄₁[i₃₂₉] == a₃₇[i₃₂₉]
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
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₃₄₁: int ::
              (  0 <= i₃₄₁
                && i₃₄₁ < i₄₀
                 ==> (exists s₃₄₂: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₃₄₁ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₃₄₁ <= x₂₀
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
                                                   ==> y₁₂ < i₃₄₁))
                                          && (y₁₃ < i₃₄₁
                                             ==> false)
                                          && x₁₅ < i₃₄₁)))
                          && (x₁₇ < i₃₄₁
                             ==> false)
                          && (s₃₄₂ == i₃₄₁
                             ==> false)
                          && 1 + i₃₄₁ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₄₁ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₄₁ < 100000
                          && a₄₁[i₃₄₁] == a₃₇[s₃₄₂]
                          &&   s₃₄₂ == i₃₄₁
                            || a₄₁[s₃₄₂] == a₃₇[i₃₄₁])
                  || (exists s₃₄₃: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₃₄₁ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₃₄₁ <= x₂₀
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
                                                   ==> y₁₂ < i₃₄₁))
                                          && (y₁₃ < i₃₄₁
                                             ==> false)
                                          && x₁₅ < i₃₄₁)))
                          && (x₁₉ < i₃₄₁
                             ==> false)
                          && s₃₄₃ == i₃₄₁
                          && 1 + i₃₄₁ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₄₁ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₄₁ < 100000)))
        && (forall i₃₄₄: int, s₃₄₅: int ::
                  0 <= i₃₄₄
                  && i₃₄₄ < i₄₀
                ||   a₄₁[i₃₄₄] == a₃₇[i₃₄₄]
                  && a₄₁[s₃₄₅] == a₃₇[s₃₄₅])
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
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₃₅₆: int ::
              (  0 <= i₃₅₆
                && i₃₅₆ < i₄₀
                 ==> (exists s₁₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₃₅₆ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₃₅₆ <= x₂₀
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
                                                   ==> y₁₂ < i₃₅₆))
                                          && (y₁₃ < i₃₅₆
                                             ==> false)
                                          && x₁₅ < i₃₅₆)))
                          && (x₁₇ < i₃₅₆
                             ==> false)
                          && (s₁₀ == i₃₅₆
                             ==> false)
                          && 1 + i₃₅₆ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₅₆ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₅₆ < 100000
                          && a₄₁[i₃₅₆] == a₃₇[s₁₀]
                          &&   s₁₀ == i₃₅₆
                            || a₄₁[s₁₀] == a₃₇[i₃₅₆])
                  || (exists s₁₀: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₃₅₆ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₃₅₆ <= x₂₀
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
                                                   ==> y₁₂ < i₃₅₆))
                                          && (y₁₃ < i₃₅₆
                                             ==> false)
                                          && x₁₅ < i₃₅₆)))
                          && (x₁₉ < i₃₅₆
                             ==> false)
                          && s₁₀ == i₃₅₆
                          && 1 + i₃₅₆ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₅₆ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₅₆ < 100000)))
        && (forall i₃₅₇: int, s₁₀: int ::
                  0 <= i₃₅₇
                  && i₃₅₇ < i₄₀
                ||   a₄₁[i₃₅₇] == a₃₇[i₃₅₇]
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
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
                        && a₃₇[i₅] == nondet_int₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₈
                || a₃₇[i₅] == a[i₅])
        && 0 <= i₄₀
        && (forall i₃₆₉: int ::
              (  0 <= i₃₆₉
                && i₃₆₉ < i₄₀
                 ==> (exists s₃₇₀: int, k₁₁: int, x₁₇: int, x₂₁: int ::
                          i₃₆₉ <= x₂₁
                          && (forall x₂₀: int ::
                                (  i₃₆₉ <= x₂₀
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
                                                   ==> y₁₂ < i₃₆₉))
                                          && (y₁₃ < i₃₆₉
                                             ==> false)
                                          && x₁₅ < i₃₆₉)))
                          && (x₁₇ < i₃₆₉
                             ==> false)
                          && (s₃₇₀ == i₃₆₉
                             ==> false)
                          && 1 + i₃₆₉ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₆₉ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₆₉ < 100000
                          && a₄₁[i₃₆₉] == a₃₇[s₃₇₀]
                          &&   s₃₇₀ == i₃₆₉
                            || a₄₁[s₃₇₀] == a₃₇[i₃₆₉])
                  || (exists s₃₇₁: int, k₁₁: int, x₁₉: int, x₂₂: int ::
                          i₃₆₉ <= x₂₂
                          && (forall x₂₀: int ::
                                (  i₃₆₉ <= x₂₀
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
                                                   ==> y₁₂ < i₃₆₉))
                                          && (y₁₃ < i₃₆₉
                                             ==> false)
                                          && x₁₅ < i₃₆₉)))
                          && (x₁₉ < i₃₆₉
                             ==> false)
                          && s₃₇₁ == i₃₆₉
                          && 1 + i₃₆₉ <= k₁₁
                          && (forall s₈: int, k₉: int ::
                                (  1 + i₃₆₉ <= k₉
                                  && k₉ < k₁₁
                                   ==> a₄₁[k₉] < a₄₁[s₈]
                                      && k₉ < 100000
                                    ||   (a₄₁[k₉] < a₄₁[s₈]
                                         ==> false)
                                      && k₉ < 100000))
                          && (k₁₁ < 100000
                             ==> false)
                          && i₃₆₉ < 100000)))
        && (forall i₃₇₂: int, s₃₇₃: int ::
                  0 <= i₃₇₂
                  && i₃₇₂ < i₄₀
                ||   a₄₁[i₃₇₂] == a₃₇[i₃₇₂]
                  && a₄₁[s₃₇₃] == a₃₇[s₃₇₃])
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
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
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
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
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

goal {:named "assert"} (forall a: [int]int, a₃₇: [int]int, i₃₈: int, i₄₀: int, a₄₁: [int]int, x₄₄: int, y₄₅: int ::
      (  0 <= i₃₈
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₈
                 ==> (exists nondet_int₁₄: int ::
                        -2147483648 <= nondet_int₁₄
                        && nondet_int₁₄ < 2147483648
                        && i₅ < 100000
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


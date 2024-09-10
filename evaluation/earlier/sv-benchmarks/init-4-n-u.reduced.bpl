data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall C: int, i₅₃: int, j₇₉: int, A₈₆: [int][int][int][int]int, k₈₇: int, A₉₂: [int][int][int][int]int, l₉₃: int, k₁₁: int ::
      (  -2147483648 <= C
        && C < 2147483648
        && 0 <= i₅₃
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₅₃
                 ==> (exists j₂₁: int ::
                        0 <= j₂₁
                        && (forall j₁₇: int ::
                              (  0 <= j₁₇
                                && j₁₇ < j₂₁
                                 ==> (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                                        0 <= k₁₄
                                        && (forall k₁₉₈: int ::
                                              (  0 <= k₁₉₈
                                                && k₁₉₈ < k₁₄
                                                 ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                                        0 <= l₉
                                                        && (forall l₇: int ::
                                                              (  0 <= l₇
                                                                && l₇ < l₉
                                                                 ==> l₇ < 2000
                                                                  && A₈[i₂₄][j₁₇][k₁₉₈][l₇] == C))
                                                        && (forall l₇: int ::
                                                                  0 <= l₇
                                                                  && l₇ < l₉
                                                                || A₈[i₂₄][j₁₇][k₁₉₈][l₇] == A₁₃[i₂₄][j₁₇][k₁₉₈][l₇])
                                                        && (l₉ < 2000
                                                           ==> false)
                                                        && k₁₉₈ < 1800)))
                                        && (k₁₄ < 1800
                                           ==> false)
                                        && j₁₇ < 1500)))
                        && (j₂₁ < 1500
                           ==> false)
                        && i₂₄ < 1000)))
        && i₅₃ < 1000
        && 0 <= j₇₉
        && (forall j₁₇: int ::
              (  0 <= j₁₇
                && j₁₇ < j₇₉
                 ==> (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                        0 <= k₁₄
                        && (forall k₁₉₉: int ::
                              (  0 <= k₁₉₉
                                && k₁₉₉ < k₁₄
                                 ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                        0 <= l₉
                                        && (forall l₇: int ::
                                              (  0 <= l₇
                                                && l₇ < l₉
                                                 ==> l₇ < 2000
                                                  && A₈[i₅₃][j₁₇][k₁₉₉][l₇] == C))
                                        && (forall l₇: int ::
                                                  0 <= l₇
                                                  && l₇ < l₉
                                                || A₈[i₅₃][j₁₇][k₁₉₉][l₇] == A₁₃[i₅₃][j₁₇][k₁₉₉][l₇])
                                        && (l₉ < 2000
                                           ==> false)
                                        && k₁₉₉ < 1800)))
                        && (k₁₄ < 1800
                           ==> false)
                        && j₁₇ < 1500)))
        && j₇₉ < 1500
        && 0 <= k₈₇
        && (forall k₂₀₀: int ::
              (  0 <= k₂₀₀
                && k₂₀₀ < k₈₇
                 ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                        0 <= l₉
                        && (forall l₇: int ::
                              (  0 <= l₇
                                && l₇ < l₉
                                 ==> l₇ < 2000
                                  && A₈[i₅₃][j₇₉][k₂₀₀][l₇] == C))
                        && (forall l₇: int ::
                                  0 <= l₇
                                  && l₇ < l₉
                                || A₈[i₅₃][j₇₉][k₂₀₀][l₇] == A₈₆[i₅₃][j₇₉][k₂₀₀][l₇])
                        && (l₉ < 2000
                           ==> false)
                        && k₂₀₀ < 1800)))
        && k₈₇ < 1800
        && 0 <= l₉₃
        && (forall l₇: int ::
              (  0 <= l₇
                && l₇ < l₉₃
                 ==> l₇ < 2000
                  && A₉₂[i₅₃][j₇₉][k₈₇][l₇] == C))
        && (forall l₇: int ::
                  0 <= l₇
                  && l₇ < l₉₃
                || A₉₂[i₅₃][j₇₉][k₈₇][l₇] == A₈₆[i₅₃][j₇₉][k₈₇][l₇])
        && 0 <= k₁₁
        && k₁₁ < k₈₇ + 1
         ==> l₉₃ < 2000
          || (exists A₈: [int][int][int][int]int, l₉: int ::
                  0 <= l₉
                  && (forall l₇: int ::
                        (  0 <= l₇
                          && l₇ < l₉
                           ==> l₇ < 2000
                            && A₈[i₅₃][j₇₉][k₁₁][l₇] == C))
                  && (forall l₇: int ::
                            0 <= l₇
                            && l₇ < l₉
                          || A₈[i₅₃][j₇₉][k₁₁][l₇] == A₉₂[i₅₃][j₇₉][k₁₁][l₇])
                  && (l₉ < 2000
                     ==> false)
                  && k₁₁ < 1800)));

goal {:named "invariant forward"} (forall C: int, i₅₃: int, j₇₉: int, A₈₆: [int][int][int][int]int, k₈₇: int, j₁₇: int ::
      (  -2147483648 <= C
        && C < 2147483648
        && 0 <= i₅₃
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₅₃
                 ==> (exists j₂₁: int ::
                        0 <= j₂₁
                        && (forall j₂₁₂: int ::
                              (  0 <= j₂₁₂
                                && j₂₁₂ < j₂₁
                                 ==> (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                                        0 <= k₁₄
                                        && (forall k₁₁: int ::
                                              (  0 <= k₁₁
                                                && k₁₁ < k₁₄
                                                 ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                                        0 <= l₉
                                                        && (forall l₇: int ::
                                                              (  0 <= l₇
                                                                && l₇ < l₉
                                                                 ==> l₇ < 2000
                                                                  && A₈[i₂₄][j₂₁₂][k₁₁][l₇] == C))
                                                        && (forall l₇: int ::
                                                                  0 <= l₇
                                                                  && l₇ < l₉
                                                                || A₈[i₂₄][j₂₁₂][k₁₁][l₇] == A₁₃[i₂₄][j₂₁₂][k₁₁][l₇])
                                                        && (l₉ < 2000
                                                           ==> false)
                                                        && k₁₁ < 1800)))
                                        && (k₁₄ < 1800
                                           ==> false)
                                        && j₂₁₂ < 1500)))
                        && (j₂₁ < 1500
                           ==> false)
                        && i₂₄ < 1000)))
        && i₅₃ < 1000
        && 0 <= j₇₉
        && (forall j₂₁₃: int ::
              (  0 <= j₂₁₃
                && j₂₁₃ < j₇₉
                 ==> (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                        0 <= k₁₄
                        && (forall k₁₁: int ::
                              (  0 <= k₁₁
                                && k₁₁ < k₁₄
                                 ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                        0 <= l₉
                                        && (forall l₇: int ::
                                              (  0 <= l₇
                                                && l₇ < l₉
                                                 ==> l₇ < 2000
                                                  && A₈[i₅₃][j₂₁₃][k₁₁][l₇] == C))
                                        && (forall l₇: int ::
                                                  0 <= l₇
                                                  && l₇ < l₉
                                                || A₈[i₅₃][j₂₁₃][k₁₁][l₇] == A₁₃[i₅₃][j₂₁₃][k₁₁][l₇])
                                        && (l₉ < 2000
                                           ==> false)
                                        && k₁₁ < 1800)))
                        && (k₁₄ < 1800
                           ==> false)
                        && j₂₁₃ < 1500)))
        && j₇₉ < 1500
        && 0 <= k₈₇
        && (forall k₁₁: int ::
              (  0 <= k₁₁
                && k₁₁ < k₈₇
                 ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                        0 <= l₉
                        && (forall l₇: int ::
                              (  0 <= l₇
                                && l₇ < l₉
                                 ==> l₇ < 2000
                                  && A₈[i₅₃][j₇₉][k₁₁][l₇] == C))
                        && (forall l₇: int ::
                                  0 <= l₇
                                  && l₇ < l₉
                                || A₈[i₅₃][j₇₉][k₁₁][l₇] == A₈₆[i₅₃][j₇₉][k₁₁][l₇])
                        && (l₉ < 2000
                           ==> false)
                        && k₁₁ < 1800)))
        && 0 <= j₁₇
        && j₁₇ < j₇₉ + 1
         ==> k₈₇ < 1800
          || (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                  0 <= k₁₄
                  && (forall k₁₁: int ::
                        (  0 <= k₁₁
                          && k₁₁ < k₁₄
                           ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                  0 <= l₉
                                  && (forall l₇: int ::
                                        (  0 <= l₇
                                          && l₇ < l₉
                                           ==> l₇ < 2000
                                            && A₈[i₅₃][j₁₇][k₁₁][l₇] == C))
                                  && (forall l₇: int ::
                                            0 <= l₇
                                            && l₇ < l₉
                                          || A₈[i₅₃][j₁₇][k₁₁][l₇] == A₁₃[i₅₃][j₁₇][k₁₁][l₇])
                                  && (l₉ < 2000
                                     ==> false)
                                  && k₁₁ < 1800)))
                  && (k₁₄ < 1800
                     ==> false)
                  && j₁₇ < 1500)));

goal {:named "invariant forward"} (forall C: int, i₅₃: int, j₇₉: int, i₂₄: int ::
      (  -2147483648 <= C
        && C < 2147483648
        && 0 <= i₅₃
        && (forall i₂₂₁: int ::
              (  0 <= i₂₂₁
                && i₂₂₁ < i₅₃
                 ==> (exists j₂₁: int ::
                        0 <= j₂₁
                        && (forall j₁₇: int ::
                              (  0 <= j₁₇
                                && j₁₇ < j₂₁
                                 ==> (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                                        0 <= k₁₄
                                        && (forall k₁₁: int ::
                                              (  0 <= k₁₁
                                                && k₁₁ < k₁₄
                                                 ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                                        0 <= l₉
                                                        && (forall l₇: int ::
                                                              (  0 <= l₇
                                                                && l₇ < l₉
                                                                 ==> l₇ < 2000
                                                                  && A₈[i₂₂₁][j₁₇][k₁₁][l₇] == C))
                                                        && (forall l₇: int ::
                                                                  0 <= l₇
                                                                  && l₇ < l₉
                                                                || A₈[i₂₂₁][j₁₇][k₁₁][l₇] == A₁₃[i₂₂₁][j₁₇][k₁₁][l₇])
                                                        && (l₉ < 2000
                                                           ==> false)
                                                        && k₁₁ < 1800)))
                                        && (k₁₄ < 1800
                                           ==> false)
                                        && j₁₇ < 1500)))
                        && (j₂₁ < 1500
                           ==> false)
                        && i₂₂₁ < 1000)))
        && i₅₃ < 1000
        && 0 <= j₇₉
        && (forall j₁₇: int ::
              (  0 <= j₁₇
                && j₁₇ < j₇₉
                 ==> (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                        0 <= k₁₄
                        && (forall k₁₁: int ::
                              (  0 <= k₁₁
                                && k₁₁ < k₁₄
                                 ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                        0 <= l₉
                                        && (forall l₇: int ::
                                              (  0 <= l₇
                                                && l₇ < l₉
                                                 ==> l₇ < 2000
                                                  && A₈[i₅₃][j₁₇][k₁₁][l₇] == C))
                                        && (forall l₇: int ::
                                                  0 <= l₇
                                                  && l₇ < l₉
                                                || A₈[i₅₃][j₁₇][k₁₁][l₇] == A₁₃[i₅₃][j₁₇][k₁₁][l₇])
                                        && (l₉ < 2000
                                           ==> false)
                                        && k₁₁ < 1800)))
                        && (k₁₄ < 1800
                           ==> false)
                        && j₁₇ < 1500)))
        && 0 <= i₂₄
        && i₂₄ < i₅₃ + 1
         ==> j₇₉ < 1500
          || (exists j₂₁: int ::
                  0 <= j₂₁
                  && (forall j₁₇: int ::
                        (  0 <= j₁₇
                          && j₁₇ < j₂₁
                           ==> (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                                  0 <= k₁₄
                                  && (forall k₁₁: int ::
                                        (  0 <= k₁₁
                                          && k₁₁ < k₁₄
                                           ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                                  0 <= l₉
                                                  && (forall l₇: int ::
                                                        (  0 <= l₇
                                                          && l₇ < l₉
                                                           ==> l₇ < 2000
                                                            && A₈[i₂₄][j₁₇][k₁₁][l₇] == C))
                                                  && (forall l₇: int ::
                                                            0 <= l₇
                                                            && l₇ < l₉
                                                          || A₈[i₂₄][j₁₇][k₁₁][l₇] == A₁₃[i₂₄][j₁₇][k₁₁][l₇])
                                                  && (l₉ < 2000
                                                     ==> false)
                                                  && k₁₁ < 1800)))
                                  && (k₁₄ < 1800
                                     ==> false)
                                  && j₁₇ < 1500)))
                  && (j₂₁ < 1500
                     ==> false)
                  && i₂₄ < 1000)));

goal {:named "assert"} (forall C: int, i₅₃: int, A₅₄: [int][int][int][int]int, i₅₉: int, j₆₂: int, k₆₈: int, l₇₂: int ::
      (  -2147483648 <= C
        && C < 2147483648
        && 0 <= i₅₃
        && (forall i₂₄: int ::
              (  0 <= i₂₄
                && i₂₄ < i₅₃
                 ==> (exists j₂₁: int ::
                        0 <= j₂₁
                        && (forall j₁₇: int ::
                              (  0 <= j₁₇
                                && j₁₇ < j₂₁
                                 ==> (exists A₁₃: [int][int][int][int]int, k₁₄: int ::
                                        0 <= k₁₄
                                        && (forall k₁₁: int ::
                                              (  0 <= k₁₁
                                                && k₁₁ < k₁₄
                                                 ==> (exists A₈: [int][int][int][int]int, l₉: int ::
                                                        0 <= l₉
                                                        && (forall l₇: int ::
                                                              (  0 <= l₇
                                                                && l₇ < l₉
                                                                 ==> l₇ < 2000
                                                                  && A₈[i₂₄][j₁₇][k₁₁][l₇] == C))
                                                        && (forall l₇: int ::
                                                                  0 <= l₇
                                                                  && l₇ < l₉
                                                                || A₈[i₂₄][j₁₇][k₁₁][l₇] == A₁₃[i₂₄][j₁₇][k₁₁][l₇])
                                                        && (l₉ < 2000
                                                           ==> false)
                                                        && k₁₁ < 1800)))
                                        && (k₁₄ < 1800
                                           ==> false)
                                        && j₁₇ < 1500)))
                        && (j₂₁ < 1500
                           ==> false)
                        && i₂₄ < 1000)))
        && 0 <= i₅₉
        && (forall i₄₆: int ::
              (  0 <= i₄₆
                && i₄₆ < i₅₉
                 ==> (exists j₄₂: int ::
                        0 <= j₄₂
                        && (forall j₃₉: int ::
                              (  0 <= j₃₉
                                && j₃₉ < j₄₂
                                 ==> (exists k₃₆: int ::
                                        0 <= k₃₆
                                        && (forall k₃₄: int ::
                                              (  0 <= k₃₄
                                                && k₃₄ < k₃₆
                                                 ==> (exists l₃₂: int ::
                                                        0 <= l₃₂
                                                        && (forall l₃₁: int ::
                                                              (  0 <= l₃₁
                                                                && l₃₁ < l₃₂
                                                                 ==> l₃₁ < 2000))
                                                        && (l₃₂ < 2000
                                                           ==> false)
                                                        && k₃₄ < 1800)))
                                        && (k₃₆ < 1800
                                           ==> false)
                                        && j₃₉ < 1500)))
                        && (j₄₂ < 1500
                           ==> false)
                        && i₄₆ < 1000)))
        && i₅₉ < 1000
        && 0 <= j₆₂
        && (forall j₃₉: int ::
              (  0 <= j₃₉
                && j₃₉ < j₆₂
                 ==> (exists k₃₆: int ::
                        0 <= k₃₆
                        && (forall k₃₄: int ::
                              (  0 <= k₃₄
                                && k₃₄ < k₃₆
                                 ==> (exists l₃₂: int ::
                                        0 <= l₃₂
                                        && (forall l₃₁: int ::
                                              (  0 <= l₃₁
                                                && l₃₁ < l₃₂
                                                 ==> l₃₁ < 2000))
                                        && (l₃₂ < 2000
                                           ==> false)
                                        && k₃₄ < 1800)))
                        && (k₃₆ < 1800
                           ==> false)
                        && j₃₉ < 1500)))
        && j₆₂ < 1500
        && 0 <= k₆₈
        && (forall k₃₄: int ::
              (  0 <= k₃₄
                && k₃₄ < k₆₈
                 ==> (exists l₃₂: int ::
                        0 <= l₃₂
                        && (forall l₃₁: int ::
                              (  0 <= l₃₁
                                && l₃₁ < l₃₂
                                 ==> l₃₁ < 2000))
                        && (l₃₂ < 2000
                           ==> false)
                        && k₃₄ < 1800)))
        && k₆₈ < 1800
        && 0 <= l₇₂
        && (forall l₃₁: int ::
              (  0 <= l₃₁
                && l₃₁ < l₇₂
                 ==> l₃₁ < 2000))
        && l₇₂ < 2000
         ==> i₅₃ < 1000
          || A₅₄[i₅₉][j₆₂][k₆₈][l₇₂] == C));


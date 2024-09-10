data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall i₅₂: int, B₈₄: [int][int][int]int, j₈₅: int, B₉₀: [int][int][int]int, k₉₁: int, j₁₁: int ::
      (  0 <= i₅₂
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₅₂
                 ==> (exists B₁₃: [int][int][int]int, j₁₄: int ::
                        0 <= j₁₄
                        && (forall j₁₅₅: int ::
                              (  0 <= j₁₅₅
                                && j₁₅₅ < j₁₄
                                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                                        0 <= k₉
                                        && (forall k₇: int ::
                                              (  0 <= k₇
                                                && k₇ < k₉
                                                 ==> (exists nondet_int₁₆: int ::
                                                        -2147483648 <= nondet_int₁₆
                                                        && nondet_int₁₆ < 2147483648
                                                        && k₇ < 1800
                                                        && B₈[i₁₇][j₁₅₅][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₇][j₁₅₅][k₇] == B₁₃[i₁₇][j₁₅₅][k₇])
                                        && (k₉ < 1800
                                           ==> false)
                                        && j₁₅₅ < 1500)))
                        && (j₁₄ < 1500
                           ==> false)
                        && i₁₇ < 1000)))
        && i₅₂ < 1000
        && 0 <= j₈₅
        && (forall j₁₅₆: int ::
              (  0 <= j₁₅₆
                && j₁₅₆ < j₈₅
                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                        0 <= k₉
                        && (forall k₇: int ::
                              (  0 <= k₇
                                && k₇ < k₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && k₇ < 1800
                                        && B₈[i₅₂][j₁₅₆][k₇] == nondet_int₁₆)))
                        && (forall k₇: int ::
                                  0 <= k₇
                                  && k₇ < k₉
                                || B₈[i₅₂][j₁₅₆][k₇] == B₈₄[i₅₂][j₁₅₆][k₇])
                        && (k₉ < 1800
                           ==> false)
                        && j₁₅₆ < 1500)))
        && j₈₅ < 1500
        && 0 <= k₉₁
        && (forall k₇: int ::
              (  0 <= k₇
                && k₇ < k₉₁
                 ==> (exists nondet_int₁₆: int ::
                        -2147483648 <= nondet_int₁₆
                        && nondet_int₁₆ < 2147483648
                        && k₇ < 1800
                        && B₉₀[i₅₂][j₈₅][k₇] == nondet_int₁₆)))
        && (forall k₇: int ::
                  0 <= k₇
                  && k₇ < k₉₁
                || B₉₀[i₅₂][j₈₅][k₇] == B₈₄[i₅₂][j₈₅][k₇])
        && 0 <= j₁₁
        && j₁₁ < j₈₅ + 1
         ==> k₉₁ < 1800
          || (exists B₈: [int][int][int]int, k₉: int ::
                  0 <= k₉
                  && (forall k₇: int ::
                        (  0 <= k₇
                          && k₇ < k₉
                           ==> (exists nondet_int₁₆: int ::
                                  -2147483648 <= nondet_int₁₆
                                  && nondet_int₁₆ < 2147483648
                                  && k₇ < 1800
                                  && B₈[i₅₂][j₁₁][k₇] == nondet_int₁₆)))
                  && (forall k₇: int ::
                            0 <= k₇
                            && k₇ < k₉
                          || B₈[i₅₂][j₁₁][k₇] == B₉₀[i₅₂][j₁₁][k₇])
                  && (k₉ < 1800
                     ==> false)
                  && j₁₁ < 1500)));

goal {:named "invariant forward"} (forall i₅₂: int, B₈₄: [int][int][int]int, j₈₅: int, i₁₇: int ::
      (  0 <= i₅₂
        && (forall i₁₆₄: int ::
              (  0 <= i₁₆₄
                && i₁₆₄ < i₅₂
                 ==> (exists B₁₃: [int][int][int]int, j₁₄: int ::
                        0 <= j₁₄
                        && (forall j₁₁: int ::
                              (  0 <= j₁₁
                                && j₁₁ < j₁₄
                                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                                        0 <= k₉
                                        && (forall k₇: int ::
                                              (  0 <= k₇
                                                && k₇ < k₉
                                                 ==> (exists nondet_int₁₆: int ::
                                                        -2147483648 <= nondet_int₁₆
                                                        && nondet_int₁₆ < 2147483648
                                                        && k₇ < 1800
                                                        && B₈[i₁₆₄][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₆₄][j₁₁][k₇] == B₁₃[i₁₆₄][j₁₁][k₇])
                                        && (k₉ < 1800
                                           ==> false)
                                        && j₁₁ < 1500)))
                        && (j₁₄ < 1500
                           ==> false)
                        && i₁₆₄ < 1000)))
        && i₅₂ < 1000
        && 0 <= j₈₅
        && (forall j₁₁: int ::
              (  0 <= j₁₁
                && j₁₁ < j₈₅
                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                        0 <= k₉
                        && (forall k₇: int ::
                              (  0 <= k₇
                                && k₇ < k₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && k₇ < 1800
                                        && B₈[i₅₂][j₁₁][k₇] == nondet_int₁₆)))
                        && (forall k₇: int ::
                                  0 <= k₇
                                  && k₇ < k₉
                                || B₈[i₅₂][j₁₁][k₇] == B₈₄[i₅₂][j₁₁][k₇])
                        && (k₉ < 1800
                           ==> false)
                        && j₁₁ < 1500)))
        && 0 <= i₁₇
        && i₁₇ < i₅₂ + 1
         ==> j₈₅ < 1500
          || (exists B₁₃: [int][int][int]int, j₁₄: int ::
                  0 <= j₁₄
                  && (forall j₁₁: int ::
                        (  0 <= j₁₁
                          && j₁₁ < j₁₄
                           ==> (exists B₈: [int][int][int]int, k₉: int ::
                                  0 <= k₉
                                  && (forall k₇: int ::
                                        (  0 <= k₇
                                          && k₇ < k₉
                                           ==> (exists nondet_int₁₆: int ::
                                                  -2147483648 <= nondet_int₁₆
                                                  && nondet_int₁₆ < 2147483648
                                                  && k₇ < 1800
                                                  && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                  && (forall k₇: int ::
                                            0 <= k₇
                                            && k₇ < k₉
                                          || B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇])
                                  && (k₉ < 1800
                                     ==> false)
                                  && j₁₁ < 1500)))
                  && (j₁₄ < 1500
                     ==> false)
                  && i₁₇ < 1000)));

goal {:named "invariant forward"} (forall B₅₁: [int][int][int]int, i₅₂: int, i₅₆: int, A₇₀: [int][int][int]int, j₇₁: int, A₇₆: [int][int][int]int, k₇₇: int, j₂₆: int ::
      (  0 <= i₅₂
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₅₂
                 ==> (exists B₁₃: [int][int][int]int, j₁₄: int ::
                        0 <= j₁₄
                        && (forall j₁₁: int ::
                              (  0 <= j₁₁
                                && j₁₁ < j₁₄
                                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                                        0 <= k₉
                                        && (forall k₇: int ::
                                              (  0 <= k₇
                                                && k₇ < k₉
                                                 ==> (exists nondet_int₁₆: int ::
                                                        -2147483648 <= nondet_int₁₆
                                                        && nondet_int₁₆ < 2147483648
                                                        && k₇ < 1800
                                                        && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇])
                                        && (k₉ < 1800
                                           ==> false)
                                        && j₁₁ < 1500)))
                        && (j₁₄ < 1500
                           ==> false)
                        && i₁₇ < 1000)))
        && 0 <= i₅₆
        && (forall i₃₂: int ::
              (  0 <= i₃₂
                && i₃₂ < i₅₆
                 ==> (exists A₂₈: [int][int][int]int, j₂₉: int ::
                        0 <= j₂₉
                        && (forall j₂₆₀: int ::
                              (  0 <= j₂₆₀
                                && j₂₆₀ < j₂₉
                                 ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                                        0 <= k₂₄
                                        && (forall k₂₂: int ::
                                              (  0 <= k₂₂
                                                && k₂₂ < k₂₄
                                                 ==> k₂₂ < 1800
                                                  && A₂₃[i₃₂][j₂₆₀][k₂₂] == B₅₁[i₃₂][j₂₆₀][k₂₂]))
                                        && (forall k₂₂: int ::
                                                  0 <= k₂₂
                                                  && k₂₂ < k₂₄
                                                || A₂₃[i₃₂][j₂₆₀][k₂₂] == A₂₈[i₃₂][j₂₆₀][k₂₂])
                                        && (k₂₄ < 1800
                                           ==> false)
                                        && j₂₆₀ < 1500)))
                        && (j₂₉ < 1500
                           ==> false)
                        && i₃₂ < 1000)))
        && i₅₆ < 1000
        && 0 <= j₇₁
        && (forall j₂₆₁: int ::
              (  0 <= j₂₆₁
                && j₂₆₁ < j₇₁
                 ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                        0 <= k₂₄
                        && (forall k₂₂: int ::
                              (  0 <= k₂₂
                                && k₂₂ < k₂₄
                                 ==> k₂₂ < 1800
                                  && A₂₃[i₅₆][j₂₆₁][k₂₂] == B₅₁[i₅₆][j₂₆₁][k₂₂]))
                        && (forall k₂₂: int ::
                                  0 <= k₂₂
                                  && k₂₂ < k₂₄
                                || A₂₃[i₅₆][j₂₆₁][k₂₂] == A₇₀[i₅₆][j₂₆₁][k₂₂])
                        && (k₂₄ < 1800
                           ==> false)
                        && j₂₆₁ < 1500)))
        && j₇₁ < 1500
        && 0 <= k₇₇
        && (forall k₂₂: int ::
              (  0 <= k₂₂
                && k₂₂ < k₇₇
                 ==> k₂₂ < 1800
                  && A₇₆[i₅₆][j₇₁][k₂₂] == B₅₁[i₅₆][j₇₁][k₂₂]))
        && (forall k₂₂: int ::
                  0 <= k₂₂
                  && k₂₂ < k₇₇
                || A₇₆[i₅₆][j₇₁][k₂₂] == A₇₀[i₅₆][j₇₁][k₂₂])
        && 0 <= j₂₆
        && j₂₆ < j₇₁ + 1
         ==> k₇₇ < 1800
          || i₅₂ < 1000
          || (exists A₂₃: [int][int][int]int, k₂₄: int ::
                  0 <= k₂₄
                  && (forall k₂₂: int ::
                        (  0 <= k₂₂
                          && k₂₂ < k₂₄
                           ==> k₂₂ < 1800
                            && A₂₃[i₅₆][j₂₆][k₂₂] == B₅₁[i₅₆][j₂₆][k₂₂]))
                  && (forall k₂₂: int ::
                            0 <= k₂₂
                            && k₂₂ < k₂₄
                          || A₂₃[i₅₆][j₂₆][k₂₂] == A₇₆[i₅₆][j₂₆][k₂₂])
                  && (k₂₄ < 1800
                     ==> false)
                  && j₂₆ < 1500)));

goal {:named "invariant forward"} (forall B₅₁: [int][int][int]int, i₅₂: int, i₅₆: int, A₇₀: [int][int][int]int, j₇₁: int, i₃₂: int ::
      (  0 <= i₅₂
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₅₂
                 ==> (exists B₁₃: [int][int][int]int, j₁₄: int ::
                        0 <= j₁₄
                        && (forall j₁₁: int ::
                              (  0 <= j₁₁
                                && j₁₁ < j₁₄
                                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                                        0 <= k₉
                                        && (forall k₇: int ::
                                              (  0 <= k₇
                                                && k₇ < k₉
                                                 ==> (exists nondet_int₁₆: int ::
                                                        -2147483648 <= nondet_int₁₆
                                                        && nondet_int₁₆ < 2147483648
                                                        && k₇ < 1800
                                                        && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇])
                                        && (k₉ < 1800
                                           ==> false)
                                        && j₁₁ < 1500)))
                        && (j₁₄ < 1500
                           ==> false)
                        && i₁₇ < 1000)))
        && 0 <= i₅₆
        && (forall i₂₇₃: int ::
              (  0 <= i₂₇₃
                && i₂₇₃ < i₅₆
                 ==> (exists A₂₈: [int][int][int]int, j₂₉: int ::
                        0 <= j₂₉
                        && (forall j₂₆: int ::
                              (  0 <= j₂₆
                                && j₂₆ < j₂₉
                                 ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                                        0 <= k₂₄
                                        && (forall k₂₂: int ::
                                              (  0 <= k₂₂
                                                && k₂₂ < k₂₄
                                                 ==> k₂₂ < 1800
                                                  && A₂₃[i₂₇₃][j₂₆][k₂₂] == B₅₁[i₂₇₃][j₂₆][k₂₂]))
                                        && (forall k₂₂: int ::
                                                  0 <= k₂₂
                                                  && k₂₂ < k₂₄
                                                || A₂₃[i₂₇₃][j₂₆][k₂₂] == A₂₈[i₂₇₃][j₂₆][k₂₂])
                                        && (k₂₄ < 1800
                                           ==> false)
                                        && j₂₆ < 1500)))
                        && (j₂₉ < 1500
                           ==> false)
                        && i₂₇₃ < 1000)))
        && i₅₆ < 1000
        && 0 <= j₇₁
        && (forall j₂₆: int ::
              (  0 <= j₂₆
                && j₂₆ < j₇₁
                 ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                        0 <= k₂₄
                        && (forall k₂₂: int ::
                              (  0 <= k₂₂
                                && k₂₂ < k₂₄
                                 ==> k₂₂ < 1800
                                  && A₂₃[i₅₆][j₂₆][k₂₂] == B₅₁[i₅₆][j₂₆][k₂₂]))
                        && (forall k₂₂: int ::
                                  0 <= k₂₂
                                  && k₂₂ < k₂₄
                                || A₂₃[i₅₆][j₂₆][k₂₂] == A₇₀[i₅₆][j₂₆][k₂₂])
                        && (k₂₄ < 1800
                           ==> false)
                        && j₂₆ < 1500)))
        && 0 <= i₃₂
        && i₃₂ < i₅₆ + 1
         ==> j₇₁ < 1500
          || i₅₂ < 1000
          || (exists A₂₈: [int][int][int]int, j₂₉: int ::
                  0 <= j₂₉
                  && (forall j₂₆: int ::
                        (  0 <= j₂₆
                          && j₂₆ < j₂₉
                           ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                                  0 <= k₂₄
                                  && (forall k₂₂: int ::
                                        (  0 <= k₂₂
                                          && k₂₂ < k₂₄
                                           ==> k₂₂ < 1800
                                            && A₂₃[i₃₂][j₂₆][k₂₂] == B₅₁[i₃₂][j₂₆][k₂₂]))
                                  && (forall k₂₂: int ::
                                            0 <= k₂₂
                                            && k₂₂ < k₂₄
                                          || A₂₃[i₃₂][j₂₆][k₂₂] == A₂₈[i₃₂][j₂₆][k₂₂])
                                  && (k₂₄ < 1800
                                     ==> false)
                                  && j₂₆ < 1500)))
                  && (j₂₉ < 1500
                     ==> false)
                  && i₃₂ < 1000)));

goal {:named "assert"} (forall B₅₁: [int][int][int]int, i₅₂: int, A₅₅: [int][int][int]int, i₅₆: int, i₅₉: int, j₆₁: int, k₆₅: int ::
      (  0 <= i₅₂
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₅₂
                 ==> (exists B₁₃: [int][int][int]int, j₁₄: int ::
                        0 <= j₁₄
                        && (forall j₁₁: int ::
                              (  0 <= j₁₁
                                && j₁₁ < j₁₄
                                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                                        0 <= k₉
                                        && (forall k₇: int ::
                                              (  0 <= k₇
                                                && k₇ < k₉
                                                 ==> (exists nondet_int₁₆: int ::
                                                        -2147483648 <= nondet_int₁₆
                                                        && nondet_int₁₆ < 2147483648
                                                        && k₇ < 1800
                                                        && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇])
                                        && (k₉ < 1800
                                           ==> false)
                                        && j₁₁ < 1500)))
                        && (j₁₄ < 1500
                           ==> false)
                        && i₁₇ < 1000)))
        && 0 <= i₅₆
        && (forall i₃₂: int ::
              (  0 <= i₃₂
                && i₃₂ < i₅₆
                 ==> (exists A₂₈: [int][int][int]int, j₂₉: int ::
                        0 <= j₂₉
                        && (forall j₂₆: int ::
                              (  0 <= j₂₆
                                && j₂₆ < j₂₉
                                 ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                                        0 <= k₂₄
                                        && (forall k₂₂: int ::
                                              (  0 <= k₂₂
                                                && k₂₂ < k₂₄
                                                 ==> k₂₂ < 1800
                                                  && A₂₃[i₃₂][j₂₆][k₂₂] == B₅₁[i₃₂][j₂₆][k₂₂]))
                                        && (forall k₂₂: int ::
                                                  0 <= k₂₂
                                                  && k₂₂ < k₂₄
                                                || A₂₃[i₃₂][j₂₆][k₂₂] == A₂₈[i₃₂][j₂₆][k₂₂])
                                        && (k₂₄ < 1800
                                           ==> false)
                                        && j₂₆ < 1500)))
                        && (j₂₉ < 1500
                           ==> false)
                        && i₃₂ < 1000)))
        && 0 <= i₅₉
        && (forall i₄₅: int ::
              (  0 <= i₄₅
                && i₄₅ < i₅₉
                 ==> (exists j₄₂: int ::
                        0 <= j₄₂
                        && (forall j₄₀: int ::
                              (  0 <= j₄₀
                                && j₄₀ < j₄₂
                                 ==> (exists k₃₈: int ::
                                        0 <= k₃₈
                                        && (forall k₃₇: int ::
                                              (  0 <= k₃₇
                                                && k₃₇ < k₃₈
                                                 ==> k₃₇ < 1800))
                                        && (k₃₈ < 1800
                                           ==> false)
                                        && j₄₀ < 1500)))
                        && (j₄₂ < 1500
                           ==> false)
                        && i₄₅ < 1000)))
        && i₅₉ < 1000
        && 0 <= j₆₁
        && (forall j₄₀: int ::
              (  0 <= j₄₀
                && j₄₀ < j₆₁
                 ==> (exists k₃₈: int ::
                        0 <= k₃₈
                        && (forall k₃₇: int ::
                              (  0 <= k₃₇
                                && k₃₇ < k₃₈
                                 ==> k₃₇ < 1800))
                        && (k₃₈ < 1800
                           ==> false)
                        && j₄₀ < 1500)))
        && j₆₁ < 1500
        && 0 <= k₆₅
        && (forall k₃₇: int ::
              (  0 <= k₃₇
                && k₃₇ < k₆₅
                 ==> k₃₇ < 1800))
        && k₆₅ < 1800
         ==> i₅₆ < 1000
          || i₅₂ < 1000
          || A₅₅[i₅₉][j₆₁][k₆₅] == B₅₁[i₅₉][j₆₁][k₆₅]));


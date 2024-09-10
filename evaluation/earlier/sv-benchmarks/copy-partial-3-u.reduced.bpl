data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall i₆₇: int, B₁₁₇: [int][int][int]int, j₁₁₈: int, B₁₂₃: [int][int][int]int, k₁₂₄: int, j₁₁: int ::
      (  500 < 1000
        && 0 <= i₆₇
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₆₇
                 ==> (exists B₁₃: [int][int][int]int, j₁₄: int ::
                        0 <= j₁₄
                        && (forall j₁₈₈: int ::
                              (  0 <= j₁₈₈
                                && j₁₈₈ < j₁₄
                                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                                        0 <= k₉
                                        && (forall k₇: int ::
                                              (  0 <= k₇
                                                && k₇ < k₉
                                                 ==> (exists nondet_int₁₆: int ::
                                                        -2147483648 <= nondet_int₁₆
                                                        && nondet_int₁₆ < 2147483648
                                                        && k₇ < 1000
                                                        && B₈[i₁₇][j₁₈₈][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₇][j₁₈₈][k₇] == B₁₃[i₁₇][j₁₈₈][k₇])
                                        && (k₉ < 1000
                                           ==> false)
                                        && j₁₈₈ < 1000)))
                        && (j₁₄ < 1000
                           ==> false)
                        && i₁₇ < 1000)))
        && i₆₇ < 1000
        && 0 <= j₁₁₈
        && (forall j₁₈₉: int ::
              (  0 <= j₁₈₉
                && j₁₈₉ < j₁₁₈
                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                        0 <= k₉
                        && (forall k₇: int ::
                              (  0 <= k₇
                                && k₇ < k₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && k₇ < 1000
                                        && B₈[i₆₇][j₁₈₉][k₇] == nondet_int₁₆)))
                        && (forall k₇: int ::
                                  0 <= k₇
                                  && k₇ < k₉
                                || B₈[i₆₇][j₁₈₉][k₇] == B₁₁₇[i₆₇][j₁₈₉][k₇])
                        && (k₉ < 1000
                           ==> false)
                        && j₁₈₉ < 1000)))
        && j₁₁₈ < 1000
        && 0 <= k₁₂₄
        && (forall k₇: int ::
              (  0 <= k₇
                && k₇ < k₁₂₄
                 ==> (exists nondet_int₁₆: int ::
                        -2147483648 <= nondet_int₁₆
                        && nondet_int₁₆ < 2147483648
                        && k₇ < 1000
                        && B₁₂₃[i₆₇][j₁₁₈][k₇] == nondet_int₁₆)))
        && (forall k₇: int ::
                  0 <= k₇
                  && k₇ < k₁₂₄
                || B₁₂₃[i₆₇][j₁₁₈][k₇] == B₁₁₇[i₆₇][j₁₁₈][k₇])
        && 0 <= j₁₁
        && j₁₁ < j₁₁₈ + 1
         ==> k₁₂₄ < 1000
          || (exists B₈: [int][int][int]int, k₉: int ::
                  0 <= k₉
                  && (forall k₇: int ::
                        (  0 <= k₇
                          && k₇ < k₉
                           ==> (exists nondet_int₁₆: int ::
                                  -2147483648 <= nondet_int₁₆
                                  && nondet_int₁₆ < 2147483648
                                  && k₇ < 1000
                                  && B₈[i₆₇][j₁₁][k₇] == nondet_int₁₆)))
                  && (forall k₇: int ::
                            0 <= k₇
                            && k₇ < k₉
                          || B₈[i₆₇][j₁₁][k₇] == B₁₂₃[i₆₇][j₁₁][k₇])
                  && (k₉ < 1000
                     ==> false)
                  && j₁₁ < 1000)));

goal {:named "invariant forward"} (forall i₆₇: int, B₁₁₇: [int][int][int]int, j₁₁₈: int, i₁₇: int ::
      (  500 < 1000
        && 0 <= i₆₇
        && (forall i₁₉₇: int ::
              (  0 <= i₁₉₇
                && i₁₉₇ < i₆₇
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
                                                        && k₇ < 1000
                                                        && B₈[i₁₉₇][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₉₇][j₁₁][k₇] == B₁₃[i₁₉₇][j₁₁][k₇])
                                        && (k₉ < 1000
                                           ==> false)
                                        && j₁₁ < 1000)))
                        && (j₁₄ < 1000
                           ==> false)
                        && i₁₉₇ < 1000)))
        && i₆₇ < 1000
        && 0 <= j₁₁₈
        && (forall j₁₁: int ::
              (  0 <= j₁₁
                && j₁₁ < j₁₁₈
                 ==> (exists B₈: [int][int][int]int, k₉: int ::
                        0 <= k₉
                        && (forall k₇: int ::
                              (  0 <= k₇
                                && k₇ < k₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && k₇ < 1000
                                        && B₈[i₆₇][j₁₁][k₇] == nondet_int₁₆)))
                        && (forall k₇: int ::
                                  0 <= k₇
                                  && k₇ < k₉
                                || B₈[i₆₇][j₁₁][k₇] == B₁₁₇[i₆₇][j₁₁][k₇])
                        && (k₉ < 1000
                           ==> false)
                        && j₁₁ < 1000)))
        && 0 <= i₁₇
        && i₁₇ < i₆₇ + 1
         ==> j₁₁₈ < 1000
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
                                                  && k₇ < 1000
                                                  && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                  && (forall k₇: int ::
                                            0 <= k₇
                                            && k₇ < k₉
                                          || B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇])
                                  && (k₉ < 1000
                                     ==> false)
                                  && j₁₁ < 1000)))
                  && (j₁₄ < 1000
                     ==> false)
                  && i₁₇ < 1000)));

goal {:named "invariant forward"} (forall B₆₆: [int][int][int]int, i₆₇: int, i₇₁: int, A₁₀₃: [int][int][int]int, j₁₀₄: int, A₁₀₉: [int][int][int]int, k₁₁₀: int, j₂₆: int ::
      (  500 < 1000
        && 0 <= i₆₇
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₆₇
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
                                                        && k₇ < 1000
                                                        && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇])
                                        && (k₉ < 1000
                                           ==> false)
                                        && j₁₁ < 1000)))
                        && (j₁₄ < 1000
                           ==> false)
                        && i₁₇ < 1000)))
        && 0 <= i₇₁
        && (forall i₃₂: int ::
              (  0 <= i₃₂
                && i₃₂ < i₇₁
                 ==> (exists A₂₈: [int][int][int]int, j₂₉: int ::
                        0 <= j₂₉
                        && (forall j₂₉₃: int ::
                              (  0 <= j₂₉₃
                                && j₂₉₃ < j₂₉
                                 ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                                        0 <= k₂₄
                                        && (forall k₂₂: int ::
                                              (  0 <= k₂₂
                                                && k₂₂ < k₂₄
                                                 ==> k₂₂ < 500
                                                  && A₂₃[i₃₂][j₂₉₃][k₂₂] == B₆₆[i₃₂][j₂₉₃][k₂₂]))
                                        && (forall k₂₂: int ::
                                                  0 <= k₂₂
                                                  && k₂₂ < k₂₄
                                                || A₂₃[i₃₂][j₂₉₃][k₂₂] == A₂₈[i₃₂][j₂₉₃][k₂₂])
                                        && (k₂₄ < 500
                                           ==> false)
                                        && j₂₉₃ < 500)))
                        && (j₂₉ < 500
                           ==> false)
                        && i₃₂ < 500)))
        && i₇₁ < 500
        && 0 <= j₁₀₄
        && (forall j₂₉₄: int ::
              (  0 <= j₂₉₄
                && j₂₉₄ < j₁₀₄
                 ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                        0 <= k₂₄
                        && (forall k₂₂: int ::
                              (  0 <= k₂₂
                                && k₂₂ < k₂₄
                                 ==> k₂₂ < 500
                                  && A₂₃[i₇₁][j₂₉₄][k₂₂] == B₆₆[i₇₁][j₂₉₄][k₂₂]))
                        && (forall k₂₂: int ::
                                  0 <= k₂₂
                                  && k₂₂ < k₂₄
                                || A₂₃[i₇₁][j₂₉₄][k₂₂] == A₁₀₃[i₇₁][j₂₉₄][k₂₂])
                        && (k₂₄ < 500
                           ==> false)
                        && j₂₉₄ < 500)))
        && j₁₀₄ < 500
        && 0 <= k₁₁₀
        && (forall k₂₂: int ::
              (  0 <= k₂₂
                && k₂₂ < k₁₁₀
                 ==> k₂₂ < 500
                  && A₁₀₉[i₇₁][j₁₀₄][k₂₂] == B₆₆[i₇₁][j₁₀₄][k₂₂]))
        && (forall k₂₂: int ::
                  0 <= k₂₂
                  && k₂₂ < k₁₁₀
                || A₁₀₉[i₇₁][j₁₀₄][k₂₂] == A₁₀₃[i₇₁][j₁₀₄][k₂₂])
        && 0 <= j₂₆
        && j₂₆ < j₁₀₄ + 1
         ==> k₁₁₀ < 500
          || i₆₇ < 1000
          || (exists A₂₃: [int][int][int]int, k₂₄: int ::
                  0 <= k₂₄
                  && (forall k₂₂: int ::
                        (  0 <= k₂₂
                          && k₂₂ < k₂₄
                           ==> k₂₂ < 500
                            && A₂₃[i₇₁][j₂₆][k₂₂] == B₆₆[i₇₁][j₂₆][k₂₂]))
                  && (forall k₂₂: int ::
                            0 <= k₂₂
                            && k₂₂ < k₂₄
                          || A₂₃[i₇₁][j₂₆][k₂₂] == A₁₀₉[i₇₁][j₂₆][k₂₂])
                  && (k₂₄ < 500
                     ==> false)
                  && j₂₆ < 500)));

goal {:named "invariant forward"} (forall B₆₆: [int][int][int]int, i₆₇: int, i₇₁: int, A₁₀₃: [int][int][int]int, j₁₀₄: int, i₃₂: int ::
      (  500 < 1000
        && 0 <= i₆₇
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₆₇
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
                                                        && k₇ < 1000
                                                        && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇])
                                        && (k₉ < 1000
                                           ==> false)
                                        && j₁₁ < 1000)))
                        && (j₁₄ < 1000
                           ==> false)
                        && i₁₇ < 1000)))
        && 0 <= i₇₁
        && (forall i₃₀₆: int ::
              (  0 <= i₃₀₆
                && i₃₀₆ < i₇₁
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
                                                 ==> k₂₂ < 500
                                                  && A₂₃[i₃₀₆][j₂₆][k₂₂] == B₆₆[i₃₀₆][j₂₆][k₂₂]))
                                        && (forall k₂₂: int ::
                                                  0 <= k₂₂
                                                  && k₂₂ < k₂₄
                                                || A₂₃[i₃₀₆][j₂₆][k₂₂] == A₂₈[i₃₀₆][j₂₆][k₂₂])
                                        && (k₂₄ < 500
                                           ==> false)
                                        && j₂₆ < 500)))
                        && (j₂₉ < 500
                           ==> false)
                        && i₃₀₆ < 500)))
        && i₇₁ < 500
        && 0 <= j₁₀₄
        && (forall j₂₆: int ::
              (  0 <= j₂₆
                && j₂₆ < j₁₀₄
                 ==> (exists A₂₃: [int][int][int]int, k₂₄: int ::
                        0 <= k₂₄
                        && (forall k₂₂: int ::
                              (  0 <= k₂₂
                                && k₂₂ < k₂₄
                                 ==> k₂₂ < 500
                                  && A₂₃[i₇₁][j₂₆][k₂₂] == B₆₆[i₇₁][j₂₆][k₂₂]))
                        && (forall k₂₂: int ::
                                  0 <= k₂₂
                                  && k₂₂ < k₂₄
                                || A₂₃[i₇₁][j₂₆][k₂₂] == A₁₀₃[i₇₁][j₂₆][k₂₂])
                        && (k₂₄ < 500
                           ==> false)
                        && j₂₆ < 500)))
        && 0 <= i₃₂
        && i₃₂ < i₇₁ + 1
         ==> j₁₀₄ < 500
          || i₆₇ < 1000
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
                                           ==> k₂₂ < 500
                                            && A₂₃[i₃₂][j₂₆][k₂₂] == B₆₆[i₃₂][j₂₆][k₂₂]))
                                  && (forall k₂₂: int ::
                                            0 <= k₂₂
                                            && k₂₂ < k₂₄
                                          || A₂₃[i₃₂][j₂₆][k₂₂] == A₂₈[i₃₂][j₂₆][k₂₂])
                                  && (k₂₄ < 500
                                     ==> false)
                                  && j₂₆ < 500)))
                  && (j₂₉ < 500
                     ==> false)
                  && i₃₂ < 500)));

goal {:named "invariant forward"} (forall B₆₆: [int][int][int]int, i₆₇: int, i₇₁: int, i₇₅: int, A₈₉: [int][int][int]int, j₉₀: int, A₉₅: [int][int][int]int, k₉₆: int, j₄₁: int ::
      (  500 < 1000
        && 0 <= i₆₇
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₆₇
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
                                                        && k₇ < 1000
                                                        && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇])
                                        && (k₉ < 1000
                                           ==> false)
                                        && j₁₁ < 1000)))
                        && (j₁₄ < 1000
                           ==> false)
                        && i₁₇ < 1000)))
        && 0 <= i₇₁
        && (forall i₃₂: int ::
              (  0 <= i₃₂
                && i₃₂ < i₇₁
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
                                                 ==> k₂₂ < 500
                                                  && A₂₃[i₃₂][j₂₆][k₂₂] == B₆₆[i₃₂][j₂₆][k₂₂]))
                                        && (forall k₂₂: int ::
                                                  0 <= k₂₂
                                                  && k₂₂ < k₂₄
                                                || A₂₃[i₃₂][j₂₆][k₂₂] == A₂₈[i₃₂][j₂₆][k₂₂])
                                        && (k₂₄ < 500
                                           ==> false)
                                        && j₂₆ < 500)))
                        && (j₂₉ < 500
                           ==> false)
                        && i₃₂ < 500)))
        && 500 <= i₇₅
        && (forall i₄₇: int ::
              (  500 <= i₄₇
                && i₄₇ < i₇₅
                 ==> (exists A₄₃: [int][int][int]int, j₄₄: int ::
                        500 <= j₄₄
                        && (forall j₄₁₉: int ::
                              (  500 <= j₄₁₉
                                && j₄₁₉ < j₄₄
                                 ==> (exists A₃₈: [int][int][int]int, k₃₉: int ::
                                        500 <= k₃₉
                                        && (forall k₃₇: int ::
                                              (  500 <= k₃₇
                                                && k₃₇ < k₃₉
                                                 ==> k₃₇ < 1000
                                                  && A₃₈[i₄₇][j₄₁₉][k₃₇] == B₆₆[i₄₇][j₄₁₉][k₃₇]))
                                        && (forall k₃₇: int ::
                                                  500 <= k₃₇
                                                  && k₃₇ < k₃₉
                                                || A₃₈[i₄₇][j₄₁₉][k₃₇] == A₄₃[i₄₇][j₄₁₉][k₃₇])
                                        && (k₃₉ < 1000
                                           ==> false)
                                        && j₄₁₉ < 1000)))
                        && (j₄₄ < 1000
                           ==> false)
                        && i₄₇ < 1000)))
        && i₇₅ < 1000
        && 500 <= j₉₀
        && (forall j₄₂₀: int ::
              (  500 <= j₄₂₀
                && j₄₂₀ < j₉₀
                 ==> (exists A₃₈: [int][int][int]int, k₃₉: int ::
                        500 <= k₃₉
                        && (forall k₃₇: int ::
                              (  500 <= k₃₇
                                && k₃₇ < k₃₉
                                 ==> k₃₇ < 1000
                                  && A₃₈[i₇₅][j₄₂₀][k₃₇] == B₆₆[i₇₅][j₄₂₀][k₃₇]))
                        && (forall k₃₇: int ::
                                  500 <= k₃₇
                                  && k₃₇ < k₃₉
                                || A₃₈[i₇₅][j₄₂₀][k₃₇] == A₈₉[i₇₅][j₄₂₀][k₃₇])
                        && (k₃₉ < 1000
                           ==> false)
                        && j₄₂₀ < 1000)))
        && j₉₀ < 1000
        && 500 <= k₉₆
        && (forall k₃₇: int ::
              (  500 <= k₃₇
                && k₃₇ < k₉₆
                 ==> k₃₇ < 1000
                  && A₉₅[i₇₅][j₉₀][k₃₇] == B₆₆[i₇₅][j₉₀][k₃₇]))
        && (forall k₃₇: int ::
                  500 <= k₃₇
                  && k₃₇ < k₉₆
                || A₉₅[i₇₅][j₉₀][k₃₇] == A₈₉[i₇₅][j₉₀][k₃₇])
        && 500 <= j₄₁
        && j₄₁ < j₉₀ + 1
         ==> k₉₆ < 1000
          || i₇₁ < 500
          || i₆₇ < 1000
          || (exists A₃₈: [int][int][int]int, k₃₉: int ::
                  500 <= k₃₉
                  && (forall k₃₇: int ::
                        (  500 <= k₃₇
                          && k₃₇ < k₃₉
                           ==> k₃₇ < 1000
                            && A₃₈[i₇₅][j₄₁][k₃₇] == B₆₆[i₇₅][j₄₁][k₃₇]))
                  && (forall k₃₇: int ::
                            500 <= k₃₇
                            && k₃₇ < k₃₉
                          || A₃₈[i₇₅][j₄₁][k₃₇] == A₉₅[i₇₅][j₄₁][k₃₇])
                  && (k₃₉ < 1000
                     ==> false)
                  && j₄₁ < 1000)));

goal {:named "invariant forward"} (forall B₆₆: [int][int][int]int, i₆₇: int, i₇₁: int, i₇₅: int, A₈₉: [int][int][int]int, j₉₀: int, i₄₇: int ::
      (  500 < 1000
        && 0 <= i₆₇
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₆₇
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
                                                        && k₇ < 1000
                                                        && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇])
                                        && (k₉ < 1000
                                           ==> false)
                                        && j₁₁ < 1000)))
                        && (j₁₄ < 1000
                           ==> false)
                        && i₁₇ < 1000)))
        && 0 <= i₇₁
        && (forall i₃₂: int ::
              (  0 <= i₃₂
                && i₃₂ < i₇₁
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
                                                 ==> k₂₂ < 500
                                                  && A₂₃[i₃₂][j₂₆][k₂₂] == B₆₆[i₃₂][j₂₆][k₂₂]))
                                        && (forall k₂₂: int ::
                                                  0 <= k₂₂
                                                  && k₂₂ < k₂₄
                                                || A₂₃[i₃₂][j₂₆][k₂₂] == A₂₈[i₃₂][j₂₆][k₂₂])
                                        && (k₂₄ < 500
                                           ==> false)
                                        && j₂₆ < 500)))
                        && (j₂₉ < 500
                           ==> false)
                        && i₃₂ < 500)))
        && 500 <= i₇₅
        && (forall i₄₃₄: int ::
              (  500 <= i₄₃₄
                && i₄₃₄ < i₇₅
                 ==> (exists A₄₃: [int][int][int]int, j₄₄: int ::
                        500 <= j₄₄
                        && (forall j₄₁: int ::
                              (  500 <= j₄₁
                                && j₄₁ < j₄₄
                                 ==> (exists A₃₈: [int][int][int]int, k₃₉: int ::
                                        500 <= k₃₉
                                        && (forall k₃₇: int ::
                                              (  500 <= k₃₇
                                                && k₃₇ < k₃₉
                                                 ==> k₃₇ < 1000
                                                  && A₃₈[i₄₃₄][j₄₁][k₃₇] == B₆₆[i₄₃₄][j₄₁][k₃₇]))
                                        && (forall k₃₇: int ::
                                                  500 <= k₃₇
                                                  && k₃₇ < k₃₉
                                                || A₃₈[i₄₃₄][j₄₁][k₃₇] == A₄₃[i₄₃₄][j₄₁][k₃₇])
                                        && (k₃₉ < 1000
                                           ==> false)
                                        && j₄₁ < 1000)))
                        && (j₄₄ < 1000
                           ==> false)
                        && i₄₃₄ < 1000)))
        && i₇₅ < 1000
        && 500 <= j₉₀
        && (forall j₄₁: int ::
              (  500 <= j₄₁
                && j₄₁ < j₉₀
                 ==> (exists A₃₈: [int][int][int]int, k₃₉: int ::
                        500 <= k₃₉
                        && (forall k₃₇: int ::
                              (  500 <= k₃₇
                                && k₃₇ < k₃₉
                                 ==> k₃₇ < 1000
                                  && A₃₈[i₇₅][j₄₁][k₃₇] == B₆₆[i₇₅][j₄₁][k₃₇]))
                        && (forall k₃₇: int ::
                                  500 <= k₃₇
                                  && k₃₇ < k₃₉
                                || A₃₈[i₇₅][j₄₁][k₃₇] == A₈₉[i₇₅][j₄₁][k₃₇])
                        && (k₃₉ < 1000
                           ==> false)
                        && j₄₁ < 1000)))
        && 500 <= i₄₇
        && i₄₇ < i₇₅ + 1
         ==> j₉₀ < 1000
          || i₇₁ < 500
          || i₆₇ < 1000
          || (exists A₄₃: [int][int][int]int, j₄₄: int ::
                  500 <= j₄₄
                  && (forall j₄₁: int ::
                        (  500 <= j₄₁
                          && j₄₁ < j₄₄
                           ==> (exists A₃₈: [int][int][int]int, k₃₉: int ::
                                  500 <= k₃₉
                                  && (forall k₃₇: int ::
                                        (  500 <= k₃₇
                                          && k₃₇ < k₃₉
                                           ==> k₃₇ < 1000
                                            && A₃₈[i₄₇][j₄₁][k₃₇] == B₆₆[i₄₇][j₄₁][k₃₇]))
                                  && (forall k₃₇: int ::
                                            500 <= k₃₇
                                            && k₃₇ < k₃₉
                                          || A₃₈[i₄₇][j₄₁][k₃₇] == A₄₃[i₄₇][j₄₁][k₃₇])
                                  && (k₃₉ < 1000
                                     ==> false)
                                  && j₄₁ < 1000)))
                  && (j₄₄ < 1000
                     ==> false)
                  && i₄₇ < 1000)));

goal {:named "assert"} (forall B₆₆: [int][int][int]int, i₆₇: int, i₇₁: int, A₇₄: [int][int][int]int, i₇₅: int, i₇₈: int, j₈₀: int, k₈₄: int ::
      (  500 < 1000
        && 0 <= i₆₇
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₆₇
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
                                                        && k₇ < 1000
                                                        && B₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || B₈[i₁₇][j₁₁][k₇] == B₁₃[i₁₇][j₁₁][k₇])
                                        && (k₉ < 1000
                                           ==> false)
                                        && j₁₁ < 1000)))
                        && (j₁₄ < 1000
                           ==> false)
                        && i₁₇ < 1000)))
        && 0 <= i₇₁
        && (forall i₃₂: int ::
              (  0 <= i₃₂
                && i₃₂ < i₇₁
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
                                                 ==> k₂₂ < 500
                                                  && A₂₃[i₃₂][j₂₆][k₂₂] == B₆₆[i₃₂][j₂₆][k₂₂]))
                                        && (forall k₂₂: int ::
                                                  0 <= k₂₂
                                                  && k₂₂ < k₂₄
                                                || A₂₃[i₃₂][j₂₆][k₂₂] == A₂₈[i₃₂][j₂₆][k₂₂])
                                        && (k₂₄ < 500
                                           ==> false)
                                        && j₂₆ < 500)))
                        && (j₂₉ < 500
                           ==> false)
                        && i₃₂ < 500)))
        && 500 <= i₇₅
        && (forall i₄₇: int ::
              (  500 <= i₄₇
                && i₄₇ < i₇₅
                 ==> (exists A₄₃: [int][int][int]int, j₄₄: int ::
                        500 <= j₄₄
                        && (forall j₄₁: int ::
                              (  500 <= j₄₁
                                && j₄₁ < j₄₄
                                 ==> (exists A₃₈: [int][int][int]int, k₃₉: int ::
                                        500 <= k₃₉
                                        && (forall k₃₇: int ::
                                              (  500 <= k₃₇
                                                && k₃₇ < k₃₉
                                                 ==> k₃₇ < 1000
                                                  && A₃₈[i₄₇][j₄₁][k₃₇] == B₆₆[i₄₇][j₄₁][k₃₇]))
                                        && (forall k₃₇: int ::
                                                  500 <= k₃₇
                                                  && k₃₇ < k₃₉
                                                || A₃₈[i₄₇][j₄₁][k₃₇] == A₄₃[i₄₇][j₄₁][k₃₇])
                                        && (k₃₉ < 1000
                                           ==> false)
                                        && j₄₁ < 1000)))
                        && (j₄₄ < 1000
                           ==> false)
                        && i₄₇ < 1000)))
        && 0 <= i₇₈
        && (forall i₆₀: int ::
              (  0 <= i₆₀
                && i₆₀ < i₇₈
                 ==> (exists j₅₇: int ::
                        0 <= j₅₇
                        && (forall j₅₅: int ::
                              (  0 <= j₅₅
                                && j₅₅ < j₅₇
                                 ==> (exists k₅₃: int ::
                                        0 <= k₅₃
                                        && (forall k₅₂: int ::
                                              (  0 <= k₅₂
                                                && k₅₂ < k₅₃
                                                 ==> k₅₂ < 1000))
                                        && (k₅₃ < 1000
                                           ==> false)
                                        && j₅₅ < 1000)))
                        && (j₅₇ < 1000
                           ==> false)
                        && i₆₀ < 1000)))
        && i₇₈ < 1000
        && 0 <= j₈₀
        && (forall j₅₅: int ::
              (  0 <= j₅₅
                && j₅₅ < j₈₀
                 ==> (exists k₅₃: int ::
                        0 <= k₅₃
                        && (forall k₅₂: int ::
                              (  0 <= k₅₂
                                && k₅₂ < k₅₃
                                 ==> k₅₂ < 1000))
                        && (k₅₃ < 1000
                           ==> false)
                        && j₅₅ < 1000)))
        && j₈₀ < 1000
        && 0 <= k₈₄
        && (forall k₅₂: int ::
              (  0 <= k₅₂
                && k₅₂ < k₈₄
                 ==> k₅₂ < 1000))
        && k₈₄ < 1000
         ==> i₇₅ < 1000
          || i₇₁ < 500
          || i₆₇ < 1000
          || A₇₄[i₇₈][j₈₀][k₈₄] == B₆₆[i₇₈][j₈₀][k₈₄]));


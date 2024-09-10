data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall i₅₅: int, A₈₉: [int][int][int]int, j₉₀: int, A₉₅: [int][int][int]int, k₉₆: int, j₁₁: int ::
      (  0 <= i₅₅
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₅₅
                 ==> (exists A₁₃: [int][int][int]int, j₁₄: int ::
                        0 <= j₁₄
                        && (forall j₁₆₀: int ::
                              (  0 <= j₁₆₀
                                && j₁₆₀ < j₁₄
                                 ==> (exists A₈: [int][int][int]int, k₉: int ::
                                        0 <= k₉
                                        && (forall k₇: int ::
                                              (  0 <= k₇
                                                && k₇ < k₉
                                                 ==> (exists nondet_int₁₆: int ::
                                                        -2147483648 <= nondet_int₁₆
                                                        && nondet_int₁₆ < 2147483648
                                                        && k₇ < 1800
                                                        && A₈[i₁₇][j₁₆₀][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || A₈[i₁₇][j₁₆₀][k₇] == A₁₃[i₁₇][j₁₆₀][k₇])
                                        && (k₉ < 1800
                                           ==> false)
                                        && j₁₆₀ < 1500)))
                        && (j₁₄ < 1500
                           ==> false)
                        && i₁₇ < 1000)))
        && i₅₅ < 1000
        && 0 <= j₉₀
        && (forall j₁₆₁: int ::
              (  0 <= j₁₆₁
                && j₁₆₁ < j₉₀
                 ==> (exists A₈: [int][int][int]int, k₉: int ::
                        0 <= k₉
                        && (forall k₇: int ::
                              (  0 <= k₇
                                && k₇ < k₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && k₇ < 1800
                                        && A₈[i₅₅][j₁₆₁][k₇] == nondet_int₁₆)))
                        && (forall k₇: int ::
                                  0 <= k₇
                                  && k₇ < k₉
                                || A₈[i₅₅][j₁₆₁][k₇] == A₈₉[i₅₅][j₁₆₁][k₇])
                        && (k₉ < 1800
                           ==> false)
                        && j₁₆₁ < 1500)))
        && j₉₀ < 1500
        && 0 <= k₉₆
        && (forall k₇: int ::
              (  0 <= k₇
                && k₇ < k₉₆
                 ==> (exists nondet_int₁₆: int ::
                        -2147483648 <= nondet_int₁₆
                        && nondet_int₁₆ < 2147483648
                        && k₇ < 1800
                        && A₉₅[i₅₅][j₉₀][k₇] == nondet_int₁₆)))
        && (forall k₇: int ::
                  0 <= k₇
                  && k₇ < k₉₆
                || A₉₅[i₅₅][j₉₀][k₇] == A₈₉[i₅₅][j₉₀][k₇])
        && 0 <= j₁₁
        && j₁₁ < j₉₀ + 1
         ==> k₉₆ < 1800
          || (exists A₈: [int][int][int]int, k₉: int ::
                  0 <= k₉
                  && (forall k₇: int ::
                        (  0 <= k₇
                          && k₇ < k₉
                           ==> (exists nondet_int₁₆: int ::
                                  -2147483648 <= nondet_int₁₆
                                  && nondet_int₁₆ < 2147483648
                                  && k₇ < 1800
                                  && A₈[i₅₅][j₁₁][k₇] == nondet_int₁₆)))
                  && (forall k₇: int ::
                            0 <= k₇
                            && k₇ < k₉
                          || A₈[i₅₅][j₁₁][k₇] == A₉₅[i₅₅][j₁₁][k₇])
                  && (k₉ < 1800
                     ==> false)
                  && j₁₁ < 1500)));

goal {:named "invariant forward"} (forall i₅₅: int, A₈₉: [int][int][int]int, j₉₀: int, i₁₇: int ::
      (  0 <= i₅₅
        && (forall i₁₆₉: int ::
              (  0 <= i₁₆₉
                && i₁₆₉ < i₅₅
                 ==> (exists A₁₃: [int][int][int]int, j₁₄: int ::
                        0 <= j₁₄
                        && (forall j₁₁: int ::
                              (  0 <= j₁₁
                                && j₁₁ < j₁₄
                                 ==> (exists A₈: [int][int][int]int, k₉: int ::
                                        0 <= k₉
                                        && (forall k₇: int ::
                                              (  0 <= k₇
                                                && k₇ < k₉
                                                 ==> (exists nondet_int₁₆: int ::
                                                        -2147483648 <= nondet_int₁₆
                                                        && nondet_int₁₆ < 2147483648
                                                        && k₇ < 1800
                                                        && A₈[i₁₆₉][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || A₈[i₁₆₉][j₁₁][k₇] == A₁₃[i₁₆₉][j₁₁][k₇])
                                        && (k₉ < 1800
                                           ==> false)
                                        && j₁₁ < 1500)))
                        && (j₁₄ < 1500
                           ==> false)
                        && i₁₆₉ < 1000)))
        && i₅₅ < 1000
        && 0 <= j₉₀
        && (forall j₁₁: int ::
              (  0 <= j₁₁
                && j₁₁ < j₉₀
                 ==> (exists A₈: [int][int][int]int, k₉: int ::
                        0 <= k₉
                        && (forall k₇: int ::
                              (  0 <= k₇
                                && k₇ < k₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && k₇ < 1800
                                        && A₈[i₅₅][j₁₁][k₇] == nondet_int₁₆)))
                        && (forall k₇: int ::
                                  0 <= k₇
                                  && k₇ < k₉
                                || A₈[i₅₅][j₁₁][k₇] == A₈₉[i₅₅][j₁₁][k₇])
                        && (k₉ < 1800
                           ==> false)
                        && j₁₁ < 1500)))
        && 0 <= i₁₇
        && i₁₇ < i₅₅ + 1
         ==> j₉₀ < 1500
          || (exists A₁₃: [int][int][int]int, j₁₄: int ::
                  0 <= j₁₄
                  && (forall j₁₁: int ::
                        (  0 <= j₁₁
                          && j₁₁ < j₁₄
                           ==> (exists A₈: [int][int][int]int, k₉: int ::
                                  0 <= k₉
                                  && (forall k₇: int ::
                                        (  0 <= k₇
                                          && k₇ < k₉
                                           ==> (exists nondet_int₁₆: int ::
                                                  -2147483648 <= nondet_int₁₆
                                                  && nondet_int₁₆ < 2147483648
                                                  && k₇ < 1800
                                                  && A₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                  && (forall k₇: int ::
                                            0 <= k₇
                                            && k₇ < k₉
                                          || A₈[i₁₇][j₁₁][k₇] == A₁₃[i₁₇][j₁₁][k₇])
                                  && (k₉ < 1800
                                     ==> false)
                                  && j₁₁ < 1500)))
                  && (j₁₄ < 1500
                     ==> false)
                  && i₁₇ < 1000)));

goal {:named "assert"} (forall A₅₄: [int][int][int]int, i₅₅: int, min₅₈: int, i₅₉: int, i₆₂: int, j₆₄: int, k₆₈: int ::
      (  0 <= i₅₅
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₅₅
                 ==> (exists A₁₃: [int][int][int]int, j₁₄: int ::
                        0 <= j₁₄
                        && (forall j₁₁: int ::
                              (  0 <= j₁₁
                                && j₁₁ < j₁₄
                                 ==> (exists A₈: [int][int][int]int, k₉: int ::
                                        0 <= k₉
                                        && (forall k₇: int ::
                                              (  0 <= k₇
                                                && k₇ < k₉
                                                 ==> (exists nondet_int₁₆: int ::
                                                        -2147483648 <= nondet_int₁₆
                                                        && nondet_int₁₆ < 2147483648
                                                        && k₇ < 1800
                                                        && A₈[i₁₇][j₁₁][k₇] == nondet_int₁₆)))
                                        && (forall k₇: int ::
                                                  0 <= k₇
                                                  && k₇ < k₉
                                                || A₈[i₁₇][j₁₁][k₇] == A₁₃[i₁₇][j₁₁][k₇])
                                        && (k₉ < 1800
                                           ==> false)
                                        && j₁₁ < 1500)))
                        && (j₁₄ < 1500
                           ==> false)
                        && i₁₇ < 1000)))
        && 0 <= i₅₉
        && (forall i₃₅: int ::
              (  0 <= i₃₅
                && i₃₅ < i₅₉
                 ==> (exists j₃₁: int ::
                        0 <= j₃₁
                        && (forall j₂₈: int ::
                              (  0 <= j₂₈
                                && j₂₈ < j₃₁
                                 ==> (exists k₂₅: int ::
                                        0 <= k₂₅
                                        && (forall min₂₂: int, k₂₃: int ::
                                              (  0 <= k₂₃
                                                && k₂₃ < k₂₅
                                                 ==> A₅₄[i₃₅][j₂₈][k₂₃] < min₂₂
                                                    && k₂₃ < 1800
                                                  ||   (A₅₄[i₃₅][j₂₈][k₂₃] < min₂₂
                                                       ==> false)
                                                    && k₂₃ < 1800))
                                        && (k₂₅ < 1800
                                           ==> false)
                                        && j₂₈ < 1500)))
                        && (j₃₁ < 1500
                           ==> false)
                        && i₃₅ < 1000)))
        && 0 <= i₆₂
        && (forall i₄₈: int ::
              (  0 <= i₄₈
                && i₄₈ < i₆₂
                 ==> (exists j₄₅: int ::
                        0 <= j₄₅
                        && (forall j₄₃: int ::
                              (  0 <= j₄₃
                                && j₄₃ < j₄₅
                                 ==> (exists k₄₁: int ::
                                        0 <= k₄₁
                                        && (forall k₄₀: int ::
                                              (  0 <= k₄₀
                                                && k₄₀ < k₄₁
                                                 ==> k₄₀ < 1800))
                                        && (k₄₁ < 1800
                                           ==> false)
                                        && j₄₃ < 1500)))
                        && (j₄₅ < 1500
                           ==> false)
                        && i₄₈ < 1000)))
        && i₆₂ < 1000
        && 0 <= j₆₄
        && (forall j₄₃: int ::
              (  0 <= j₄₃
                && j₄₃ < j₆₄
                 ==> (exists k₄₁: int ::
                        0 <= k₄₁
                        && (forall k₄₀: int ::
                              (  0 <= k₄₀
                                && k₄₀ < k₄₁
                                 ==> k₄₀ < 1800))
                        && (k₄₁ < 1800
                           ==> false)
                        && j₄₃ < 1500)))
        && j₆₄ < 1500
        && 0 <= k₆₈
        && (forall k₄₀: int ::
              (  0 <= k₄₀
                && k₄₀ < k₆₈
                 ==> k₄₀ < 1800))
        && k₆₈ < 1800
         ==> i₅₉ < 1000
          || i₅₅ < 1000
          || min₅₈ <= A₅₄[i₆₂][j₆₄][k₆₈]));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall C: int, i₃₆: int, A₅₀: [int][int][int]int, j₅₁: int, A₅₆: [int][int][int]int, k₅₇: int, j₁₀: int ::
      (  0 <= C
        && C < 4294967296
        && 0 <= i₃₆
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₃₆
                 ==> (exists A₁₂: [int][int][int]int, j₁₃: int ::
                        0 <= j₁₃
                        && (forall j₁₄₃: int ::
                              (  0 <= j₁₄₃
                                && j₁₄₃ < j₁₃
                                 ==> (exists A₇: [int][int][int]int, k₈: int ::
                                        0 <= k₈
                                        && (forall k₆: int ::
                                              (  0 <= k₆
                                                && k₆ < k₈
                                                 ==> k₆ < 1000
                                                  && A₇[i₁₆][j₁₄₃][k₆] == j₁₄₃ + k₆ + i₁₆ + C))
                                        && (forall k₆: int ::
                                                  0 <= k₆
                                                  && k₆ < k₈
                                                || A₇[i₁₆][j₁₄₃][k₆] == A₁₂[i₁₆][j₁₄₃][k₆])
                                        && (k₈ < 1000
                                           ==> false)
                                        && j₁₄₃ < 1000)))
                        && (j₁₃ < 1000
                           ==> false)
                        && i₁₆ < 1000)))
        && i₃₆ < 1000
        && 0 <= j₅₁
        && (forall j₁₄₄: int ::
              (  0 <= j₁₄₄
                && j₁₄₄ < j₅₁
                 ==> (exists A₇: [int][int][int]int, k₈: int ::
                        0 <= k₈
                        && (forall k₆: int ::
                              (  0 <= k₆
                                && k₆ < k₈
                                 ==> k₆ < 1000
                                  && A₇[i₃₆][j₁₄₄][k₆] == j₁₄₄ + k₆ + i₃₆ + C))
                        && (forall k₆: int ::
                                  0 <= k₆
                                  && k₆ < k₈
                                || A₇[i₃₆][j₁₄₄][k₆] == A₅₀[i₃₆][j₁₄₄][k₆])
                        && (k₈ < 1000
                           ==> false)
                        && j₁₄₄ < 1000)))
        && j₅₁ < 1000
        && 0 <= k₅₇
        && (forall k₆: int ::
              (  0 <= k₆
                && k₆ < k₅₇
                 ==> k₆ < 1000
                  && A₅₆[i₃₆][j₅₁][k₆] == j₅₁ + k₆ + i₃₆ + C))
        && (forall k₆: int ::
                  0 <= k₆
                  && k₆ < k₅₇
                || A₅₆[i₃₆][j₅₁][k₆] == A₅₀[i₃₆][j₅₁][k₆])
        && 0 <= j₁₀
        && j₁₀ < j₅₁ + 1
         ==> k₅₇ < 1000
          || (exists A₇: [int][int][int]int, k₈: int ::
                  0 <= k₈
                  && (forall k₆: int ::
                        (  0 <= k₆
                          && k₆ < k₈
                           ==> k₆ < 1000
                            && A₇[i₃₆][j₁₀][k₆] == j₁₀ + k₆ + i₃₆ + C))
                  && (forall k₆: int ::
                            0 <= k₆
                            && k₆ < k₈
                          || A₇[i₃₆][j₁₀][k₆] == A₅₆[i₃₆][j₁₀][k₆])
                  && (k₈ < 1000
                     ==> false)
                  && j₁₀ < 1000)));

goal {:named "invariant forward"} (forall C: int, i₃₆: int, A₅₀: [int][int][int]int, j₅₁: int, i₁₆: int ::
      (  0 <= C
        && C < 4294967296
        && 0 <= i₃₆
        && (forall i₁₅₄: int ::
              (  0 <= i₁₅₄
                && i₁₅₄ < i₃₆
                 ==> (exists A₁₂: [int][int][int]int, j₁₃: int ::
                        0 <= j₁₃
                        && (forall j₁₀: int ::
                              (  0 <= j₁₀
                                && j₁₀ < j₁₃
                                 ==> (exists A₇: [int][int][int]int, k₈: int ::
                                        0 <= k₈
                                        && (forall k₆: int ::
                                              (  0 <= k₆
                                                && k₆ < k₈
                                                 ==> k₆ < 1000
                                                  && A₇[i₁₅₄][j₁₀][k₆] == j₁₀ + k₆ + i₁₅₄ + C))
                                        && (forall k₆: int ::
                                                  0 <= k₆
                                                  && k₆ < k₈
                                                || A₇[i₁₅₄][j₁₀][k₆] == A₁₂[i₁₅₄][j₁₀][k₆])
                                        && (k₈ < 1000
                                           ==> false)
                                        && j₁₀ < 1000)))
                        && (j₁₃ < 1000
                           ==> false)
                        && i₁₅₄ < 1000)))
        && i₃₆ < 1000
        && 0 <= j₅₁
        && (forall j₁₀: int ::
              (  0 <= j₁₀
                && j₁₀ < j₅₁
                 ==> (exists A₇: [int][int][int]int, k₈: int ::
                        0 <= k₈
                        && (forall k₆: int ::
                              (  0 <= k₆
                                && k₆ < k₈
                                 ==> k₆ < 1000
                                  && A₇[i₃₆][j₁₀][k₆] == j₁₀ + k₆ + i₃₆ + C))
                        && (forall k₆: int ::
                                  0 <= k₆
                                  && k₆ < k₈
                                || A₇[i₃₆][j₁₀][k₆] == A₅₀[i₃₆][j₁₀][k₆])
                        && (k₈ < 1000
                           ==> false)
                        && j₁₀ < 1000)))
        && 0 <= i₁₆
        && i₁₆ < i₃₆ + 1
         ==> j₅₁ < 1000
          || (exists A₁₂: [int][int][int]int, j₁₃: int ::
                  0 <= j₁₃
                  && (forall j₁₀: int ::
                        (  0 <= j₁₀
                          && j₁₀ < j₁₃
                           ==> (exists A₇: [int][int][int]int, k₈: int ::
                                  0 <= k₈
                                  && (forall k₆: int ::
                                        (  0 <= k₆
                                          && k₆ < k₈
                                           ==> k₆ < 1000
                                            && A₇[i₁₆][j₁₀][k₆] == j₁₀ + k₆ + i₁₆ + C))
                                  && (forall k₆: int ::
                                            0 <= k₆
                                            && k₆ < k₈
                                          || A₇[i₁₆][j₁₀][k₆] == A₁₂[i₁₆][j₁₀][k₆])
                                  && (k₈ < 1000
                                     ==> false)
                                  && j₁₀ < 1000)))
                  && (j₁₃ < 1000
                     ==> false)
                  && i₁₆ < 1000)));

goal {:named "assert"} (forall C: int, A₃₅: [int][int][int]int, i₃₆: int, i₃₉: int, j₄₁: int, k₄₅: int ::
      (  0 <= C
        && C < 4294967296
        && 0 <= i₃₆
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₃₆
                 ==> (exists A₁₂: [int][int][int]int, j₁₃: int ::
                        0 <= j₁₃
                        && (forall j₁₀: int ::
                              (  0 <= j₁₀
                                && j₁₀ < j₁₃
                                 ==> (exists A₇: [int][int][int]int, k₈: int ::
                                        0 <= k₈
                                        && (forall k₆: int ::
                                              (  0 <= k₆
                                                && k₆ < k₈
                                                 ==> k₆ < 1000
                                                  && A₇[i₁₆][j₁₀][k₆] == j₁₀ + k₆ + i₁₆ + C))
                                        && (forall k₆: int ::
                                                  0 <= k₆
                                                  && k₆ < k₈
                                                || A₇[i₁₆][j₁₀][k₆] == A₁₂[i₁₆][j₁₀][k₆])
                                        && (k₈ < 1000
                                           ==> false)
                                        && j₁₀ < 1000)))
                        && (j₁₃ < 1000
                           ==> false)
                        && i₁₆ < 1000)))
        && 0 <= i₃₉
        && (forall i₂₉: int ::
              (  0 <= i₂₉
                && i₂₉ < i₃₉
                 ==> (exists j₂₆: int ::
                        0 <= j₂₆
                        && (forall j₂₄: int ::
                              (  0 <= j₂₄
                                && j₂₄ < j₂₆
                                 ==> (exists k₂₂: int ::
                                        0 <= k₂₂
                                        && (forall k₂₁: int ::
                                              (  0 <= k₂₁
                                                && k₂₁ < k₂₂
                                                 ==> k₂₁ < 1000))
                                        && (k₂₂ < 1000
                                           ==> false)
                                        && j₂₄ < 1000)))
                        && (j₂₆ < 1000
                           ==> false)
                        && i₂₉ < 1000)))
        && i₃₉ < 1000
        && 0 <= j₄₁
        && (forall j₂₄: int ::
              (  0 <= j₂₄
                && j₂₄ < j₄₁
                 ==> (exists k₂₂: int ::
                        0 <= k₂₂
                        && (forall k₂₁: int ::
                              (  0 <= k₂₁
                                && k₂₁ < k₂₂
                                 ==> k₂₁ < 1000))
                        && (k₂₂ < 1000
                           ==> false)
                        && j₂₄ < 1000)))
        && j₄₁ < 1000
        && 0 <= k₄₅
        && (forall k₂₁: int ::
              (  0 <= k₂₁
                && k₂₁ < k₄₅
                 ==> k₂₁ < 1000))
        && k₄₅ < 1000
         ==> i₃₆ < 1000
          || A₃₅[i₃₉][j₄₁][k₄₅] == i₃₉ + j₄₁ + k₄₅ + C));


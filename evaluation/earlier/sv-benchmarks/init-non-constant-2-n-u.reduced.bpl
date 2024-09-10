data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall C: int, q₂₃: int, s₂₄: int, A₂₆: [int][int]int, i₂₇: int, A₃₄: [int][int]int, j₃₅: int, i₁₃: int ::
      (  q₂₃ < 1000
        && s₂₄ < 1500
        && 0 <= i₂₇
        && (forall i₁₃₁: int ::
              (  0 <= i₁₃₁
                && i₁₃₁ < i₂₇
                 ==> (exists A₁₀: [int][int]int, j₁₁: int ::
                        0 <= j₁₁
                        && (forall j₉: int ::
                              (  0 <= j₉
                                && j₉ < j₁₁
                                 ==> j₉ < s₂₄
                                  && A₁₀[i₁₃₁][j₉] == i₁₃₁ + j₉ + C))
                        && (forall j₉: int ::
                                  0 <= j₉
                                  && j₉ < j₁₁
                                || A₁₀[i₁₃₁][j₉] == A₂₆[i₁₃₁][j₉])
                        && (j₁₁ < s₂₄
                           ==> false)
                        && i₁₃₁ < q₂₃)))
        && i₂₇ < q₂₃
        && 0 <= j₃₅
        && (forall j₉: int ::
              (  0 <= j₉
                && j₉ < j₃₅
                 ==> j₉ < s₂₄
                  && A₃₄[i₂₇][j₉] == j₉ + i₂₇ + C))
        && (forall j₉: int ::
                  0 <= j₉
                  && j₉ < j₃₅
                || A₃₄[i₂₇][j₉] == A₂₆[i₂₇][j₉])
        && 0 <= i₁₃
        && i₁₃ < i₂₇ + 1
         ==> j₃₅ < s₂₄
          || (exists A₁₀: [int][int]int, j₁₁: int ::
                  0 <= j₁₁
                  && (forall j₉: int ::
                        (  0 <= j₉
                          && j₉ < j₁₁
                           ==> j₉ < s₂₄
                            && A₁₀[i₁₃][j₉] == i₁₃ + j₉ + C))
                  && (forall j₉: int ::
                            0 <= j₉
                            && j₉ < j₁₁
                          || A₁₀[i₁₃][j₉] == A₃₄[i₁₃][j₉])
                  && (j₁₁ < s₂₄
                     ==> false)
                  && i₁₃ < q₂₃)));

goal {:named "assert"} (forall C: int, q₂₃: int, s₂₄: int, A₂₆: [int][int]int, i₂₇: int, i₂₉: int, j₃₀: int ::
      (  q₂₃ < 1000
        && s₂₄ < 1500
        && 0 <= i₂₇
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₇
                 ==> (exists A₁₀: [int][int]int, j₁₁: int ::
                        0 <= j₁₁
                        && (forall j₉: int ::
                              (  0 <= j₉
                                && j₉ < j₁₁
                                 ==> j₉ < s₂₄
                                  && A₁₀[i₁₃][j₉] == i₁₃ + j₉ + C))
                        && (forall j₉: int ::
                                  0 <= j₉
                                  && j₉ < j₁₁
                                || A₁₀[i₁₃][j₉] == A₂₆[i₁₃][j₉])
                        && (j₁₁ < s₂₄
                           ==> false)
                        && i₁₃ < q₂₃)))
        && 0 <= i₂₉
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₂₉
                 ==> (exists j₁₈: int ::
                        0 <= j₁₈
                        && (forall j₁₇: int ::
                              (  0 <= j₁₇
                                && j₁₇ < j₁₈
                                 ==> j₁₇ < s₂₄))
                        && (j₁₈ < s₂₄
                           ==> false)
                        && i₂₀ < q₂₃)))
        && i₂₉ < q₂₃
        && 0 <= j₃₀
        && (forall j₁₇: int ::
              (  0 <= j₁₇
                && j₁₇ < j₃₀
                 ==> j₁₇ < s₂₄))
        && j₃₀ < s₂₄
         ==> i₂₇ < q₂₃
          || A₂₆[i₂₉][j₃₀] == i₂₉ + j₃₀ + C));


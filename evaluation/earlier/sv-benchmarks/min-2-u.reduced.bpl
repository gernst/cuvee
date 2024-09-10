data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall A₃₁: [int][int]int, i₃₂: int, A₅₁: [int][int]int, j₅₂: int, i₁₀: int ::
      (  0 <= i₃₂
        && (forall i₁₀₂: int ::
              (  0 <= i₁₀₂
                && i₁₀₂ < i₃₂
                 ==> (exists A₇: [int][int]int, j₈: int ::
                        0 <= j₈
                        && (forall j₆: int ::
                              (  0 <= j₆
                                && j₆ < j₈
                                 ==> (exists nondet_int₁₅: int ::
                                        j₆ < 1500
                                        && A₇[i₁₀₂][j₆] == nondet_int₁₅)))
                        && (forall j₆: int ::
                                  0 <= j₆
                                  && j₆ < j₈
                                || A₇[i₁₀₂][j₆] == A₃₁[i₁₀₂][j₆])
                        && (j₈ < 1500
                           ==> false)
                        && i₁₀₂ < 1000)))
        && i₃₂ < 1000
        && 0 <= j₅₂
        && (forall j₆: int ::
              (  0 <= j₆
                && j₆ < j₅₂
                 ==> (exists nondet_int₁₅: int ::
                        j₆ < 1500
                        && A₅₁[i₃₂][j₆] == nondet_int₁₅)))
        && (forall j₆: int ::
                  0 <= j₆
                  && j₆ < j₅₂
                || A₅₁[i₃₂][j₆] == A₃₁[i₃₂][j₆])
        && 0 <= i₁₀
        && i₁₀ < i₃₂ + 1
         ==> j₅₂ < 1500
          || (exists A₇: [int][int]int, j₈: int ::
                  0 <= j₈
                  && (forall j₆: int ::
                        (  0 <= j₆
                          && j₆ < j₈
                           ==> (exists nondet_int₁₅: int ::
                                  j₆ < 1500
                                  && A₇[i₁₀][j₆] == nondet_int₁₅)))
                  && (forall j₆: int ::
                            0 <= j₆
                            && j₆ < j₈
                          || A₇[i₁₀][j₆] == A₅₁[i₁₀][j₆])
                  && (j₈ < 1500
                     ==> false)
                  && i₁₀ < 1000)));

goal {:named "assert"} (forall A₃₁: [int][int]int, i₃₂: int, min₃₄: int, i₃₅: int, i₃₇: int, j₃₈: int ::
      (  0 <= i₃₂
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> (exists A₇: [int][int]int, j₈: int ::
                        0 <= j₈
                        && (forall j₆: int ::
                              (  0 <= j₆
                                && j₆ < j₈
                                 ==> (exists nondet_int₁₅: int ::
                                        j₆ < 1500
                                        && A₇[i₁₀][j₆] == nondet_int₁₅)))
                        && (forall j₆: int ::
                                  0 <= j₆
                                  && j₆ < j₈
                                || A₇[i₁₀][j₆] == A₃₁[i₁₀][j₆])
                        && (j₈ < 1500
                           ==> false)
                        && i₁₀ < 1000)))
        && 0 <= i₃₅
        && (forall i₂₀: int ::
              (  0 <= i₂₀
                && i₂₀ < i₃₅
                 ==> (exists j₁₇: int ::
                        0 <= j₁₇
                        && (forall min₁₄: int, j₁₅: int ::
                              (  0 <= j₁₅
                                && j₁₅ < j₁₇
                                 ==> A₃₁[i₂₀][j₁₅] < min₁₄
                                    && j₁₅ < 1500
                                  ||   (A₃₁[i₂₀][j₁₅] < min₁₄
                                       ==> false)
                                    && j₁₅ < 1500))
                        && (j₁₇ < 1500
                           ==> false)
                        && i₂₀ < 1500)))
        && 0 <= i₃₇
        && (forall i₂₇: int ::
              (  0 <= i₂₇
                && i₂₇ < i₃₇
                 ==> (exists j₂₅: int ::
                        0 <= j₂₅
                        && (forall j₂₄: int ::
                              (  0 <= j₂₄
                                && j₂₄ < j₂₅
                                 ==> j₂₄ < 1500))
                        && (j₂₅ < 1500
                           ==> false)
                        && i₂₇ < 1500)))
        && i₃₇ < 1500
        && 0 <= j₃₈
        && (forall j₂₄: int ::
              (  0 <= j₂₄
                && j₂₄ < j₃₈
                 ==> j₂₄ < 1500))
        && j₃₈ < 1500
         ==> i₃₅ < 1500
          || i₃₂ < 1000
          || min₃₄ <= A₃₁[i₃₇][j₃₈]));


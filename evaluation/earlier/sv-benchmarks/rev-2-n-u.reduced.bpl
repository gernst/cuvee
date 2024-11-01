data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall B₂₉: [int][int]int, i₃₀: int, B₄₇: [int][int]int, j₄₈: int, i₁₀: int ::
      (  0 <= i₃₀
        && (forall i₉₈: int ::
              (  0 <= i₉₈
                && i₉₈ < i₃₀
                 ==> (exists B₇: [int][int]int, j₈: int ::
                        0 <= j₈
                        && (forall j₆: int ::
                              (  0 <= j₆
                                && j₆ < j₈
                                 ==> (exists nondet_int₁₅: int ::
                                        j₆ < 1500
                                        && B₇[i₉₈][j₆] == nondet_int₁₅)))
                        && (forall j₆: int ::
                                  0 <= j₆
                                  && j₆ < j₈
                                || B₇[i₉₈][j₆] == B₂₉[i₉₈][j₆])
                        && (j₈ < 1500
                           ==> false)
                        && i₉₈ < 1000)))
        && i₃₀ < 1000
        && 0 <= j₄₈
        && (forall j₆: int ::
              (  0 <= j₆
                && j₆ < j₄₈
                 ==> (exists nondet_int₁₅: int ::
                        j₆ < 1500
                        && B₄₇[i₃₀][j₆] == nondet_int₁₅)))
        && (forall j₆: int ::
                  0 <= j₆
                  && j₆ < j₄₈
                || B₄₇[i₃₀][j₆] == B₂₉[i₃₀][j₆])
        && 0 <= i₁₀
        && i₁₀ < i₃₀ + 1
         ==> j₄₈ < 1500
          || (exists B₇: [int][int]int, j₈: int ::
                  0 <= j₈
                  && (forall j₆: int ::
                        (  0 <= j₆
                          && j₆ < j₈
                           ==> (exists nondet_int₁₅: int ::
                                  j₆ < 1500
                                  && B₇[i₁₀][j₆] == nondet_int₁₅)))
                  && (forall j₆: int ::
                            0 <= j₆
                            && j₆ < j₈
                          || B₇[i₁₀][j₆] == B₄₇[i₁₀][j₆])
                  && (j₈ < 1500
                     ==> false)
                  && i₁₀ < 1000)));

goal {:named "invariant forward"} (forall B₂₉: [int][int]int, i₃₀: int, A₃₂: [int][int]int, i₃₃: int, A₄₀: [int][int]int, j₄₁: int, i₁₈: int ::
      (  0 <= i₃₀
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₃₀
                 ==> (exists B₇: [int][int]int, j₈: int ::
                        0 <= j₈
                        && (forall j₆: int ::
                              (  0 <= j₆
                                && j₆ < j₈
                                 ==> (exists nondet_int₁₅: int ::
                                        j₆ < 1500
                                        && B₇[i₁₀][j₆] == nondet_int₁₅)))
                        && (forall j₆: int ::
                                  0 <= j₆
                                  && j₆ < j₈
                                || B₇[i₁₀][j₆] == B₂₉[i₁₀][j₆])
                        && (j₈ < 1500
                           ==> false)
                        && i₁₀ < 1000)))
        && 0 <= i₃₃
        && (forall i₁₇₆: int ::
              (  0 <= i₁₇₆
                && i₁₇₆ < i₃₃
                 ==> (exists A₁₅: [int][int]int, j₁₆: int ::
                        0 <= j₁₆
                        && (forall j₁₄: int ::
                              (  0 <= j₁₄
                                && j₁₄ < j₁₆
                                 ==> j₁₄ < 1500
                                  && A₁₅[i₁₇₆][j₁₄] == B₂₉[-1 + 1000 + -i₁₇₆][-1 + -j₁₄ + 1500]))
                        && (forall j₁₄: int ::
                                  0 <= j₁₄
                                  && j₁₄ < j₁₆
                                || A₁₅[i₁₇₆][j₁₄] == A₃₂[i₁₇₆][j₁₄])
                        && (j₁₆ < 1500
                           ==> false)
                        && i₁₇₆ < 1000)))
        && i₃₃ < 1000
        && 0 <= j₄₁
        && (forall j₁₄: int ::
              (  0 <= j₁₄
                && j₁₄ < j₄₁
                 ==> j₁₄ < 1500
                  && A₄₀[i₃₃][j₁₄] == B₂₉[-1 + -i₃₃ + 1000][-1 + -j₁₄ + 1500]))
        && (forall j₁₄: int ::
                  0 <= j₁₄
                  && j₁₄ < j₄₁
                || A₄₀[i₃₃][j₁₄] == A₃₂[i₃₃][j₁₄])
        && 0 <= i₁₈
        && i₁₈ < i₃₃ + 1
         ==> j₄₁ < 1500
          || i₃₀ < 1000
          || (exists A₁₅: [int][int]int, j₁₆: int ::
                  0 <= j₁₆
                  && (forall j₁₄: int ::
                        (  0 <= j₁₄
                          && j₁₄ < j₁₆
                           ==> j₁₄ < 1500
                            && A₁₅[i₁₈][j₁₄] == B₂₉[-1 + 1000 + -i₁₈][-1 + -j₁₄ + 1500]))
                  && (forall j₁₄: int ::
                            0 <= j₁₄
                            && j₁₄ < j₁₆
                          || A₁₅[i₁₈][j₁₄] == A₄₀[i₁₈][j₁₄])
                  && (j₁₆ < 1500
                     ==> false)
                  && i₁₈ < 1000)));

goal {:named "assert"} (forall B₂₉: [int][int]int, i₃₀: int, A₃₂: [int][int]int, i₃₃: int, i₃₅: int, j₃₆: int ::
      (  0 <= i₃₀
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₃₀
                 ==> (exists B₇: [int][int]int, j₈: int ::
                        0 <= j₈
                        && (forall j₆: int ::
                              (  0 <= j₆
                                && j₆ < j₈
                                 ==> (exists nondet_int₁₅: int ::
                                        j₆ < 1500
                                        && B₇[i₁₀][j₆] == nondet_int₁₅)))
                        && (forall j₆: int ::
                                  0 <= j₆
                                  && j₆ < j₈
                                || B₇[i₁₀][j₆] == B₂₉[i₁₀][j₆])
                        && (j₈ < 1500
                           ==> false)
                        && i₁₀ < 1000)))
        && 0 <= i₃₃
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₃₃
                 ==> (exists A₁₅: [int][int]int, j₁₆: int ::
                        0 <= j₁₆
                        && (forall j₁₄: int ::
                              (  0 <= j₁₄
                                && j₁₄ < j₁₆
                                 ==> j₁₄ < 1500
                                  && A₁₅[i₁₈][j₁₄] == B₂₉[-1 + 1000 + -i₁₈][-1 + -j₁₄ + 1500]))
                        && (forall j₁₄: int ::
                                  0 <= j₁₄
                                  && j₁₄ < j₁₆
                                || A₁₅[i₁₈][j₁₄] == A₃₂[i₁₈][j₁₄])
                        && (j₁₆ < 1500
                           ==> false)
                        && i₁₈ < 1000)))
        && 0 <= i₃₅
        && (forall i₂₅: int ::
              (  0 <= i₂₅
                && i₂₅ < i₃₅
                 ==> (exists j₂₃: int ::
                        0 <= j₂₃
                        && (forall j₂₂: int ::
                              (  0 <= j₂₂
                                && j₂₂ < j₂₃
                                 ==> j₂₂ < 1500))
                        && (j₂₃ < 1500
                           ==> false)
                        && i₂₅ < 1000)))
        && i₃₅ < 1000
        && 0 <= j₃₆
        && (forall j₂₂: int ::
              (  0 <= j₂₂
                && j₂₂ < j₃₆
                 ==> j₂₂ < 1500))
        && j₃₆ < 1500
         ==> i₃₃ < 1000
          || i₃₀ < 1000
          || A₃₂[i₃₅][j₃₆] == B₂₉[1000 - i₃₅ - 1][1500 - j₃₆ - 1]));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall B₂₉: [int][int]int, i₃₀: int, B₄₇: [int][int]int, j₄₈: int, i₁₀: int ::
      (  500 < 1000
        && 700 < 1500
        && 0 <= i₃₀
        && (forall i₉₉: int ::
              (  0 <= i₉₉
                && i₉₉ < i₃₀
                 ==> (exists B₇: [int][int]int, j₈: int ::
                        0 <= j₈
                        && (forall j₆: int ::
                              (  0 <= j₆
                                && j₆ < j₈
                                 ==> (exists nondet_int₁₅: int ::
                                        -2147483648 <= nondet_int₁₅
                                        && nondet_int₁₅ < 2147483648
                                        && j₆ < 1500
                                        && B₇[i₉₉][j₆] == nondet_int₁₅)))
                        && (forall j₆: int ::
                                  0 <= j₆
                                  && j₆ < j₈
                                || B₇[i₉₉][j₆] == B₂₉[i₉₉][j₆])
                        && (j₈ < 1500
                           ==> false)
                        && i₉₉ < 1000)))
        && i₃₀ < 1000
        && 0 <= j₄₈
        && (forall j₆: int ::
              (  0 <= j₆
                && j₆ < j₄₈
                 ==> (exists nondet_int₁₅: int ::
                        -2147483648 <= nondet_int₁₅
                        && nondet_int₁₅ < 2147483648
                        && j₆ < 1500
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
                                  -2147483648 <= nondet_int₁₅
                                  && nondet_int₁₅ < 2147483648
                                  && j₆ < 1500
                                  && B₇[i₁₀][j₆] == nondet_int₁₅)))
                  && (forall j₆: int ::
                            0 <= j₆
                            && j₆ < j₈
                          || B₇[i₁₀][j₆] == B₄₇[i₁₀][j₆])
                  && (j₈ < 1500
                     ==> false)
                  && i₁₀ < 1000)));

goal {:named "invariant forward"} (forall B₂₉: [int][int]int, i₃₀: int, A₃₂: [int][int]int, i₃₃: int, A₄₀: [int][int]int, j₄₁: int, i₁₈: int ::
      (  500 < 1000
        && 700 < 1500
        && 0 <= i₃₀
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₃₀
                 ==> (exists B₇: [int][int]int, j₈: int ::
                        0 <= j₈
                        && (forall j₆: int ::
                              (  0 <= j₆
                                && j₆ < j₈
                                 ==> (exists nondet_int₁₅: int ::
                                        -2147483648 <= nondet_int₁₅
                                        && nondet_int₁₅ < 2147483648
                                        && j₆ < 1500
                                        && B₇[i₁₀][j₆] == nondet_int₁₅)))
                        && (forall j₆: int ::
                                  0 <= j₆
                                  && j₆ < j₈
                                || B₇[i₁₀][j₆] == B₂₉[i₁₀][j₆])
                        && (j₈ < 1500
                           ==> false)
                        && i₁₀ < 1000)))
        && 0 <= i₃₃
        && (forall i₁₇₇: int ::
              (  0 <= i₁₇₇
                && i₁₇₇ < i₃₃
                 ==> (exists A₁₅: [int][int]int, j₁₆: int ::
                        0 <= j₁₆
                        && (forall j₁₄: int ::
                              (  0 <= j₁₄
                                && j₁₄ < j₁₆
                                 ==> j₁₄ < 700
                                  && A₁₅[i₁₇₇][j₁₄] == B₂₉[i₁₇₇][j₁₄]))
                        && (forall j₁₄: int ::
                                  0 <= j₁₄
                                  && j₁₄ < j₁₆
                                || A₁₅[i₁₇₇][j₁₄] == A₃₂[i₁₇₇][j₁₄])
                        && (j₁₆ < 700
                           ==> false)
                        && i₁₇₇ < 500)))
        && i₃₃ < 500
        && 0 <= j₄₁
        && (forall j₁₄: int ::
              (  0 <= j₁₄
                && j₁₄ < j₄₁
                 ==> j₁₄ < 700
                  && A₄₀[i₃₃][j₁₄] == B₂₉[i₃₃][j₁₄]))
        && (forall j₁₄: int ::
                  0 <= j₁₄
                  && j₁₄ < j₄₁
                || A₄₀[i₃₃][j₁₄] == A₃₂[i₃₃][j₁₄])
        && 0 <= i₁₈
        && i₁₈ < i₃₃ + 1
         ==> j₄₁ < 700
          || i₃₀ < 1000
          || (exists A₁₅: [int][int]int, j₁₆: int ::
                  0 <= j₁₆
                  && (forall j₁₄: int ::
                        (  0 <= j₁₄
                          && j₁₄ < j₁₆
                           ==> j₁₄ < 700
                            && A₁₅[i₁₈][j₁₄] == B₂₉[i₁₈][j₁₄]))
                  && (forall j₁₄: int ::
                            0 <= j₁₄
                            && j₁₄ < j₁₆
                          || A₁₅[i₁₈][j₁₄] == A₄₀[i₁₈][j₁₄])
                  && (j₁₆ < 700
                     ==> false)
                  && i₁₈ < 500)));

goal {:named "assert"} (forall B₂₉: [int][int]int, i₃₀: int, A₃₂: [int][int]int, i₃₃: int, i₃₅: int, j₃₆: int ::
      (  500 < 1000
        && 700 < 1500
        && 0 <= i₃₀
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₃₀
                 ==> (exists B₇: [int][int]int, j₈: int ::
                        0 <= j₈
                        && (forall j₆: int ::
                              (  0 <= j₆
                                && j₆ < j₈
                                 ==> (exists nondet_int₁₅: int ::
                                        -2147483648 <= nondet_int₁₅
                                        && nondet_int₁₅ < 2147483648
                                        && j₆ < 1500
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
                                 ==> j₁₄ < 700
                                  && A₁₅[i₁₈][j₁₄] == B₂₉[i₁₈][j₁₄]))
                        && (forall j₁₄: int ::
                                  0 <= j₁₄
                                  && j₁₄ < j₁₆
                                || A₁₅[i₁₈][j₁₄] == A₃₂[i₁₈][j₁₄])
                        && (j₁₆ < 700
                           ==> false)
                        && i₁₈ < 500)))
        && 0 <= i₃₅
        && (forall i₂₅: int ::
              (  0 <= i₂₅
                && i₂₅ < i₃₅
                 ==> (exists j₂₃: int ::
                        0 <= j₂₃
                        && (forall j₂₂: int ::
                              (  0 <= j₂₂
                                && j₂₂ < j₂₃
                                 ==> j₂₂ < 700))
                        && (j₂₃ < 700
                           ==> false)
                        && i₂₅ < 500)))
        && i₃₅ < 500
        && 0 <= j₃₆
        && (forall j₂₂: int ::
              (  0 <= j₂₂
                && j₂₂ < j₃₆
                 ==> j₂₂ < 700))
        && j₃₆ < 700
         ==> i₃₃ < 500
          || i₃₀ < 1000
          || A₃₂[i₃₅][j₃₆] == B₂₉[i₃₅][j₃₆]));


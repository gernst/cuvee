data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall A₃₀: [int][int]int, i₃₁: int, A₄₈: [int][int]int, j₄₉: int, i₁₁: int ::
      (  0 <= i₃₁
        && (forall i₁₀₀: int ::
              (  0 <= i₁₀₀
                && i₁₀₀ < i₃₁
                 ==> (exists A₈: [int][int]int, j₉: int ::
                        0 <= j₉
                        && (forall j₇: int ::
                              (  0 <= j₇
                                && j₇ < j₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && j₇ < 1000
                                        && A₈[i₁₀₀][j₇] == nondet_int₁₆)))
                        && (forall j₇: int ::
                                  0 <= j₇
                                  && j₇ < j₉
                                || A₈[i₁₀₀][j₇] == A₃₀[i₁₀₀][j₇])
                        && (j₉ < 1000
                           ==> false)
                        && i₁₀₀ < 1000)))
        && i₃₁ < 1000
        && 0 <= j₄₉
        && (forall j₇: int ::
              (  0 <= j₇
                && j₇ < j₄₉
                 ==> (exists nondet_int₁₆: int ::
                        -2147483648 <= nondet_int₁₆
                        && nondet_int₁₆ < 2147483648
                        && j₇ < 1000
                        && A₄₈[i₃₁][j₇] == nondet_int₁₆)))
        && (forall j₇: int ::
                  0 <= j₇
                  && j₇ < j₄₉
                || A₄₈[i₃₁][j₇] == A₃₀[i₃₁][j₇])
        && 0 <= i₁₁
        && i₁₁ < i₃₁ + 1
         ==> j₄₉ < 1000
          || (exists A₈: [int][int]int, j₉: int ::
                  0 <= j₉
                  && (forall j₇: int ::
                        (  0 <= j₇
                          && j₇ < j₉
                           ==> (exists nondet_int₁₆: int ::
                                  -2147483648 <= nondet_int₁₆
                                  && nondet_int₁₆ < 2147483648
                                  && j₇ < 1000
                                  && A₈[i₁₁][j₇] == nondet_int₁₆)))
                  && (forall j₇: int ::
                            0 <= j₇
                            && j₇ < j₉
                          || A₈[i₁₁][j₇] == A₄₈[i₁₁][j₇])
                  && (j₉ < 1000
                     ==> false)
                  && i₁₁ < 1000)));

goal {:named "invariant forward"} (forall A₃₀: [int][int]int, i₃₁: int, C₃₃: [int][int]int, i₃₄: int, C₄₁: [int][int]int, j₄₂: int, i₁₉: int ::
      (  0 <= i₃₁
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₃₁
                 ==> (exists A₈: [int][int]int, j₉: int ::
                        0 <= j₉
                        && (forall j₇: int ::
                              (  0 <= j₇
                                && j₇ < j₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && j₇ < 1000
                                        && A₈[i₁₁][j₇] == nondet_int₁₆)))
                        && (forall j₇: int ::
                                  0 <= j₇
                                  && j₇ < j₉
                                || A₈[i₁₁][j₇] == A₃₀[i₁₁][j₇])
                        && (j₉ < 1000
                           ==> false)
                        && i₁₁ < 1000)))
        && 0 <= i₃₄
        && (forall i₁₇₈: int ::
              (  0 <= i₁₇₈
                && i₁₇₈ < i₃₄
                 ==> (exists C₁₆: [int][int]int, j₁₇: int ::
                        0 <= j₁₇
                        && (forall j₁₅: int ::
                              (  0 <= j₁₅
                                && j₁₅ < j₁₇
                                 ==> j₁₅ < 1000
                                  && C₁₆[j₁₅][i₁₇₈] == A₃₀[i₁₇₈][j₁₅]))
                        && (forall j₁₅: int ::
                                  0 <= j₁₅
                                  && j₁₅ < j₁₇
                                || C₁₆[j₁₅][i₁₇₈] == C₃₃[j₁₅][i₁₇₈])
                        && (j₁₇ < 1000
                           ==> false)
                        && i₁₇₈ < 1000)))
        && i₃₄ < 1000
        && 0 <= j₄₂
        && (forall j₁₅: int ::
              (  0 <= j₁₅
                && j₁₅ < j₄₂
                 ==> j₁₅ < 1000
                  && C₄₁[j₁₅][i₃₄] == A₃₀[i₃₄][j₁₅]))
        && (forall j₁₅: int ::
                  0 <= j₁₅
                  && j₁₅ < j₄₂
                || C₄₁[j₁₅][i₃₄] == C₃₃[j₁₅][i₃₄])
        && 0 <= i₁₉
        && i₁₉ < i₃₄ + 1
         ==> j₄₂ < 1000
          || i₃₁ < 1000
          || (exists C₁₆: [int][int]int, j₁₇: int ::
                  0 <= j₁₇
                  && (forall j₁₅: int ::
                        (  0 <= j₁₅
                          && j₁₅ < j₁₇
                           ==> j₁₅ < 1000
                            && C₁₆[j₁₅][i₁₉] == A₃₀[i₁₉][j₁₅]))
                  && (forall j₁₅: int ::
                            0 <= j₁₅
                            && j₁₅ < j₁₇
                          || C₁₆[j₁₅][i₁₉] == C₄₁[j₁₅][i₁₉])
                  && (j₁₇ < 1000
                     ==> false)
                  && i₁₉ < 1000)));

goal {:named "assert"} (forall A₃₀: [int][int]int, i₃₁: int, C₃₃: [int][int]int, i₃₄: int, i₃₆: int, j₃₇: int ::
      (  0 <= i₃₁
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₃₁
                 ==> (exists A₈: [int][int]int, j₉: int ::
                        0 <= j₉
                        && (forall j₇: int ::
                              (  0 <= j₇
                                && j₇ < j₉
                                 ==> (exists nondet_int₁₆: int ::
                                        -2147483648 <= nondet_int₁₆
                                        && nondet_int₁₆ < 2147483648
                                        && j₇ < 1000
                                        && A₈[i₁₁][j₇] == nondet_int₁₆)))
                        && (forall j₇: int ::
                                  0 <= j₇
                                  && j₇ < j₉
                                || A₈[i₁₁][j₇] == A₃₀[i₁₁][j₇])
                        && (j₉ < 1000
                           ==> false)
                        && i₁₁ < 1000)))
        && 0 <= i₃₄
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₃₄
                 ==> (exists C₁₆: [int][int]int, j₁₇: int ::
                        0 <= j₁₇
                        && (forall j₁₅: int ::
                              (  0 <= j₁₅
                                && j₁₅ < j₁₇
                                 ==> j₁₅ < 1000
                                  && C₁₆[j₁₅][i₁₉] == A₃₀[i₁₉][j₁₅]))
                        && (forall j₁₅: int ::
                                  0 <= j₁₅
                                  && j₁₅ < j₁₇
                                || C₁₆[j₁₅][i₁₉] == C₃₃[j₁₅][i₁₉])
                        && (j₁₇ < 1000
                           ==> false)
                        && i₁₉ < 1000)))
        && 0 <= i₃₆
        && (forall i₂₆: int ::
              (  0 <= i₂₆
                && i₂₆ < i₃₆
                 ==> (exists j₂₄: int ::
                        0 <= j₂₄
                        && (forall j₂₃: int ::
                              (  0 <= j₂₃
                                && j₂₃ < j₂₄
                                 ==> j₂₃ < 1000))
                        && (j₂₄ < 1000
                           ==> false)
                        && i₂₆ < 1000)))
        && i₃₆ < 1000
        && 0 <= j₃₇
        && (forall j₂₃: int ::
              (  0 <= j₂₃
                && j₂₃ < j₃₇
                 ==> j₂₃ < 1000))
        && j₃₇ < 1000
         ==> i₃₄ < 1000
          || i₃₁ < 1000
          || C₃₃[j₃₇][i₃₆] == A₃₀[i₃₆][j₃₇]));


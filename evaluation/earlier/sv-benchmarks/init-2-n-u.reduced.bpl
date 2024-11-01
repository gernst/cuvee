data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall C: int, A₂₀: [int][int]int, i₂₁: int, A₂₈: [int][int]int, j₂₉: int, i₉: int ::
      (  0 <= i₂₁
        && (forall i₉₇: int ::
              (  0 <= i₉₇
                && i₉₇ < i₂₁
                 ==> (exists A₆: [int][int]int, j₇: int ::
                        0 <= j₇
                        && (forall j₅: int ::
                              (  0 <= j₅
                                && j₅ < j₇
                                 ==> j₅ < 1500
                                  && A₆[i₉₇][j₅] == C))
                        && (forall j₅: int ::
                                  0 <= j₅
                                  && j₅ < j₇
                                || A₆[i₉₇][j₅] == A₂₀[i₉₇][j₅])
                        && (j₇ < 1500
                           ==> false)
                        && i₉₇ < 1000)))
        && i₂₁ < 1000
        && 0 <= j₂₉
        && (forall j₅: int ::
              (  0 <= j₅
                && j₅ < j₂₉
                 ==> j₅ < 1500
                  && A₂₈[i₂₁][j₅] == C))
        && (forall j₅: int ::
                  0 <= j₅
                  && j₅ < j₂₉
                || A₂₈[i₂₁][j₅] == A₂₀[i₂₁][j₅])
        && 0 <= i₉
        && i₉ < i₂₁ + 1
         ==> j₂₉ < 1500
          || (exists A₆: [int][int]int, j₇: int ::
                  0 <= j₇
                  && (forall j₅: int ::
                        (  0 <= j₅
                          && j₅ < j₇
                           ==> j₅ < 1500
                            && A₆[i₉][j₅] == C))
                  && (forall j₅: int ::
                            0 <= j₅
                            && j₅ < j₇
                          || A₆[i₉][j₅] == A₂₈[i₉][j₅])
                  && (j₇ < 1500
                     ==> false)
                  && i₉ < 1000)));

goal {:named "assert"} (forall C: int, A₂₀: [int][int]int, i₂₁: int, i₂₃: int, j₂₄: int ::
      (  0 <= i₂₁
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₁
                 ==> (exists A₆: [int][int]int, j₇: int ::
                        0 <= j₇
                        && (forall j₅: int ::
                              (  0 <= j₅
                                && j₅ < j₇
                                 ==> j₅ < 1500
                                  && A₆[i₉][j₅] == C))
                        && (forall j₅: int ::
                                  0 <= j₅
                                  && j₅ < j₇
                                || A₆[i₉][j₅] == A₂₀[i₉][j₅])
                        && (j₇ < 1500
                           ==> false)
                        && i₉ < 1000)))
        && 0 <= i₂₃
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₂₃
                 ==> (exists j₁₄: int ::
                        0 <= j₁₄
                        && (forall j₁₃: int ::
                              (  0 <= j₁₃
                                && j₁₃ < j₁₄
                                 ==> j₁₃ < 1500))
                        && (j₁₄ < 1500
                           ==> false)
                        && i₁₆ < 1000)))
        && i₂₃ < 1000
        && 0 <= j₂₄
        && (forall j₁₃: int ::
              (  0 <= j₁₃
                && j₁₃ < j₂₄
                 ==> j₁₃ < 1500))
        && j₂₄ < 1500
         ==> i₂₁ < 1000
          || A₂₀[i₂₃][j₂₄] == C));


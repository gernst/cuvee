data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₂₅: [int][int]int, row₂₆: int, array₃₇: [int][int]int, column₃₈: int, row₁₀: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₂₆
        && (forall row₁₂₃: int ::
              (  0 <= row₁₂₃
                && row₁₂₃ < row₂₆
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> (exists diff₂₅: int ::
                                        column₆ < nondet_short₁
                                        && array₇[row₁₂₃][column₆] == diff₂₅)))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₁₂₃][column₆] == array₂₅[row₁₂₃][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₂₃ < nondet_short₁)))
        && row₂₆ < nondet_short₁
        && 0 <= column₃₈
        && (forall column₆: int ::
              (  0 <= column₆
                && column₆ < column₃₈
                 ==> (exists diff₂₅: int ::
                        column₆ < nondet_short₁
                        && array₃₇[row₂₆][column₆] == diff₂₅)))
        && (forall column₆: int ::
                  0 <= column₆
                  && column₆ < column₃₈
                || array₃₇[row₂₆][column₆] == array₂₅[row₂₆][column₆])
        && 0 <= row₁₀
        && row₁₀ < row₂₆ + 1
         ==> column₃₈ < nondet_short₁
          || (exists array₇: [int][int]int, column₈: int ::
                  0 <= column₈
                  && (forall column₆: int ::
                        (  0 <= column₆
                          && column₆ < column₈
                           ==> (exists diff₂₅: int ::
                                  column₆ < nondet_short₁
                                  && array₇[row₁₀][column₆] == diff₂₅)))
                  && (forall column₆: int ::
                            0 <= column₆
                            && column₆ < column₈
                          || array₇[row₁₀][column₆] == array₃₇[row₁₀][column₆])
                  && (column₈ < nondet_short₁
                     ==> false)
                  && row₁₀ < nondet_short₁)));

goal {:named "assert"} (forall nondet_short₁: int, array₂₅: [int][int]int, row₂₆: int, sum₂₈: int, row₂₉: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₂₆
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₂₆
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> (exists diff₂₅: int ::
                                        column₆ < nondet_short₁
                                        && array₇[row₁₀][column₆] == diff₂₅)))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₁₀][column₆] == array₂₅[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && 0 <= row₂₉
        && (forall row₂₀: int ::
              (  0 <= row₂₀
                && row₂₀ < row₂₉
                 ==> (exists column₁₇: int ::
                        0 <= column₁₇
                        && (forall column₁₅: int ::
                              (  0 <= column₁₅
                                && column₁₅ < column₁₇
                                 ==> column₁₅ < nondet_short₁))
                        && (column₁₇ < nondet_short₁
                           ==> false)
                        && row₂₀ < nondet_short₁)))
         ==> row₂₉ < nondet_short₁
          || row₂₆ < nondet_short₁
          || 3 * sum₂₈ == nondet_short₁ * (nondet_short₁ - 1) * (nondet_short₁ + 1)));


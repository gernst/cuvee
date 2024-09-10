data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₃₇: [int][int]int, row₃₈: int, array₈₃: [int][int]int, column₈₄: int, row₁₀: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₃₈
        && (forall row₁₅₃: int ::
              (  0 <= row₁₅₃
                && row₁₅₃ < row₃₈
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> column₆ < nondet_short₁
                                  && array₇[row₁₅₃][column₆] == 0))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₁₅₃][column₆] == array₃₇[row₁₅₃][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₅₃ < nondet_short₁)))
        && row₃₈ < nondet_short₁
        && 0 <= column₈₄
        && (forall column₆: int ::
              (  0 <= column₆
                && column₆ < column₈₄
                 ==> column₆ < nondet_short₁
                  && array₈₃[row₃₈][column₆] == 0))
        && (forall column₆: int ::
                  0 <= column₆
                  && column₆ < column₈₄
                || array₈₃[row₃₈][column₆] == array₃₇[row₃₈][column₆])
        && 0 <= row₁₀
        && row₁₀ < row₃₈ + 1
         ==> column₈₄ < nondet_short₁
          || (exists array₇: [int][int]int, column₈: int ::
                  0 <= column₈
                  && (forall column₆: int ::
                        (  0 <= column₆
                          && column₆ < column₈
                           ==> column₆ < nondet_short₁
                            && array₇[row₁₀][column₆] == 0))
                  && (forall column₆: int ::
                            0 <= column₆
                            && column₆ < column₈
                          || array₇[row₁₀][column₆] == array₈₃[row₁₀][column₆])
                  && (column₈ < nondet_short₁
                     ==> false)
                  && row₁₀ < nondet_short₁)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₃₇: [int][int]int, row₃₈: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₃₈
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₃₈
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> column₆ < nondet_short₁
                                  && array₇[row₁₀][column₆] == 0))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₁₀][column₆] == array₃₇[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
         ==> row₃₈ < nondet_short₁
          || (exists nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₁₇: int ::
                  (temp₁₇ == 0
                     ==> false)
                  && -2147483648 <= temp₁₇
                  && temp₁₇ < 2147483648
                  && nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁
                  && 0 <= nondet_short₅₁₅
                  && nondet_short₅₁₅ < nondet_short₁
                  && 0 <= nondet_short₄₁₄
                  && nondet_short₄₁₄ < nondet_short₁
                  && -32768 <= nondet_short₅₁₅
                  && nondet_short₅₁₅ < 32768
                  && -32768 <= nondet_short₄₁₄
                  && nondet_short₄₁₄ < 32768
                  && array₃₇[nondet_short₄₁₄][nondet_short₅₁₅] == (-1) * (-1) * (-1) * (-1))
          || (exists nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₁₈: int ::
                  (temp₁₈ == 0
                     ==> false)
                  && -2147483648 <= temp₁₈
                  && temp₁₈ < 2147483648
                  && (nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁
                     ==> false)
                  && 0 <= nondet_short₅₁₅
                  && nondet_short₅₁₅ < nondet_short₁
                  && 0 <= nondet_short₄₁₄
                  && nondet_short₄₁₄ < nondet_short₁
                  && -32768 <= nondet_short₅₁₅
                  && nondet_short₅₁₅ < 32768
                  && -32768 <= nondet_short₄₁₄
                  && nondet_short₄₁₄ < 32768)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₃₇: [int][int]int, row₃₈: int, nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₁₇: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₃₈
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₃₈
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> column₆ < nondet_short₁
                                  && array₇[row₁₀][column₆] == 0))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₁₀][column₆] == array₃₇[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₁₇ == 0
        && -2147483648 <= temp₁₇
        && temp₁₇ < 2147483648
        && nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁
        && 0 <= nondet_short₅₁₅
        && nondet_short₅₁₅ < nondet_short₁
        && 0 <= nondet_short₄₁₄
        && nondet_short₄₁₄ < nondet_short₁
        && -32768 <= nondet_short₅₁₅
        && nondet_short₅₁₅ < 32768
        && -32768 <= nondet_short₄₁₄
        && nondet_short₄₁₄ < 32768
         ==> row₃₈ < nondet_short₁));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₃₇: [int][int]int, row₃₈: int, nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₁₈: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₃₈
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₃₈
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> column₆ < nondet_short₁
                                  && array₇[row₁₀][column₆] == 0))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₁₀][column₆] == array₃₇[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₁₈ == 0
        && -2147483648 <= temp₁₈
        && temp₁₈ < 2147483648
        && 0 <= nondet_short₅₁₅
        && nondet_short₅₁₅ < nondet_short₁
        && 0 <= nondet_short₄₁₄
        && nondet_short₄₁₄ < nondet_short₁
        && -32768 <= nondet_short₅₁₅
        && nondet_short₅₁₅ < 32768
        && -32768 <= nondet_short₄₁₄
        && nondet_short₄₁₄ < 32768
         ==> row₃₈ < nondet_short₁
          || nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁));


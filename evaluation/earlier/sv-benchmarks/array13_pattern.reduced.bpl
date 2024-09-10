data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₃₇: [int][int]int, row₃₈: int, array₈₅: [int][int]int, column₈₆: int, row₁₀: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₃₈
        && (forall row₁₅₅: int ::
              (  0 <= row₁₅₅
                && row₁₅₅ < row₃₈
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> column₆ < nondet_short₁
                                  && array₇[row₁₅₅][column₆] == 0))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₁₅₅][column₆] == array₃₇[row₁₅₅][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₅₅ < nondet_short₁)))
        && row₃₈ < nondet_short₁
        && 0 <= column₈₆
        && (forall column₆: int ::
              (  0 <= column₆
                && column₆ < column₈₆
                 ==> column₆ < nondet_short₁
                  && array₈₅[row₃₈][column₆] == 0))
        && (forall column₆: int ::
                  0 <= column₆
                  && column₆ < column₈₆
                || array₈₅[row₃₈][column₆] == array₃₇[row₃₈][column₆])
        && 0 <= row₁₀
        && row₁₀ < row₃₈ + 1
         ==> column₈₆ < nondet_short₁
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
                          || array₇[row₁₀][column₆] == array₈₅[row₁₀][column₆])
                  && (column₈ < nondet_short₁
                     ==> false)
                  && row₁₀ < nondet_short₁)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₃₇: [int][int]int, row₃₈: int, index1₁₄: int, index2₁₅: int, temp₁₇: int ::
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
        && index2₁₅ < index1₁₄
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
        && -32768 <= index2₁₅
        && index2₁₅ < 32768
        && -32768 <= index1₁₄
        && index1₁₄ < 32768
         ==> row₃₈ < nondet_short₁));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₃₇: [int][int]int, row₃₈: int, index1₁₄: int, index2₁₅: int, temp₁₈: int ::
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
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
        && -32768 <= index2₁₅
        && index2₁₅ < 32768
        && -32768 <= index1₁₄
        && index1₁₄ < 32768
         ==> row₃₈ < nondet_short₁
          || index2₁₅ < index1₁₄));


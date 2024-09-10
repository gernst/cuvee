data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₃₅: [int][int]int, row₃₆: int, array₆₈: [int][int]int, column₆₉: int, row₁₀: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₃₆
        && (forall row₁₃₈: int ::
              (  0 <= row₁₃₈
                && row₁₃₈ < row₃₆
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> column₆ < nondet_short₁
                                  && array₇[row₁₃₈][column₆] == 0))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₁₃₈][column₆] == array₃₅[row₁₃₈][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₃₈ < nondet_short₁)))
        && row₃₆ < nondet_short₁
        && 0 <= column₆₉
        && (forall column₆: int ::
              (  0 <= column₆
                && column₆ < column₆₉
                 ==> column₆ < nondet_short₁
                  && array₆₈[row₃₆][column₆] == 0))
        && (forall column₆: int ::
                  0 <= column₆
                  && column₆ < column₆₉
                || array₆₈[row₃₆][column₆] == array₃₅[row₃₆][column₆])
        && 0 <= row₁₀
        && row₁₀ < row₃₆ + 1
         ==> column₆₉ < nondet_short₁
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
                          || array₇[row₁₀][column₆] == array₆₈[row₁₀][column₆])
                  && (column₈ < nondet_short₁
                     ==> false)
                  && row₁₀ < nondet_short₁)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₃₅: [int][int]int, row₃₆: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₃₆
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₃₆
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
                                || array₇[row₁₀][column₆] == array₃₅[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
         ==> row₃₆ < nondet_short₁
          || (exists index1₁₄: int, index2₁₅: int, temp₁₆: int ::
                  (temp₁₆ == 0
                     ==> false)
                  && -2147483648 <= temp₁₆
                  && temp₁₆ < 2147483648
                  && 0 <= index2₁₅
                  && index2₁₅ < nondet_short₁
                  && 0 <= index1₁₄
                  && index1₁₄ < nondet_short₁
                  && -32768 <= index2₁₅
                  && index2₁₅ < 32768
                  && -32768 <= index1₁₄
                  && index1₁₄ < 32768
                  && array₃₅[index2₁₅][index1₁₄] == (-1) * (-1)
                  &&   index2₁₅ == index1₁₄
                    || index1₁₄ == index2₁₅
                    || array₃₅[index1₁₄][index2₁₅] == (-1) * (-1) * (-1))));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₃₅: [int][int]int, row₃₆: int, index1₁₄: int, index2₁₅: int, temp₁₆: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₃₆
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₃₆
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
                                || array₇[row₁₀][column₆] == array₃₅[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₁₆ == 0
        && -2147483648 <= temp₁₆
        && temp₁₆ < 2147483648
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
        && -32768 <= index2₁₅
        && index2₁₅ < 32768
        && -32768 <= index1₁₄
        && index1₁₄ < 32768
         ==> row₃₆ < nondet_short₁));


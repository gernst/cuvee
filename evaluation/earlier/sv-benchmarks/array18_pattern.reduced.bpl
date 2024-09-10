data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₄₁: [int][int]int, row₄₂: int, array₁₁₉: [int][int]int, column₁₂₀: int, row₁₀: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₄₂
        && (forall row₁₈₉: int ::
              (  0 <= row₁₈₉
                && row₁₈₉ < row₄₂
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> column₆ < nondet_short₁
                                  && array₇[row₁₈₉][column₆] == 0))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₁₈₉][column₆] == array₄₁[row₁₈₉][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₈₉ < nondet_short₁)))
        && row₄₂ < nondet_short₁
        && 0 <= column₁₂₀
        && (forall column₆: int ::
              (  0 <= column₆
                && column₆ < column₁₂₀
                 ==> column₆ < nondet_short₁
                  && array₁₁₉[row₄₂][column₆] == 0))
        && (forall column₆: int ::
                  0 <= column₆
                  && column₆ < column₁₂₀
                || array₁₁₉[row₄₂][column₆] == array₄₁[row₄₂][column₆])
        && 0 <= row₁₀
        && row₁₀ < row₄₂ + 1
         ==> column₁₂₀ < nondet_short₁
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
                          || array₇[row₁₀][column₆] == array₁₁₉[row₁₀][column₆])
                  && (column₈ < nondet_short₁
                     ==> false)
                  && row₁₀ < nondet_short₁)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₄₁: [int][int]int, row₄₂: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₄₂
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₄₂
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
                                || array₇[row₁₀][column₆] == array₄₁[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
         ==> row₄₂ < nondet_short₁
          || (exists index1₁₄: int, index2₁₅: int, temp₁₉: int ::
                  (temp₁₉ == 0
                     ==> false)
                  && -2147483648 <= temp₁₉
                  && temp₁₉ < 2147483648
                  && index1₁₄ == index2₁₅
                  && 0 <= index2₁₅
                  && index2₁₅ < nondet_short₁
                  && 0 <= index1₁₄
                  && index1₁₄ < nondet_short₁
                  && -32768 <= index2₁₅
                  && index2₁₅ < 32768
                  && -32768 <= index1₁₄
                  && index1₁₄ < 32768
                  && array₄₁[-1 + -index1₁₄ + nondet_short₁][index2₁₅] == (-1) * (-1) * (-1) * (-1))
          || (exists index1₁₄: int, index2₁₅: int, temp₂₀: int ::
                  (temp₂₀ == 0
                     ==> false)
                  && -2147483648 <= temp₂₀
                  && temp₂₀ < 2147483648
                  && index1₁₄ == index2₁₅
                  && (index1₁₄ == index2₁₅
                     ==> false)
                  && 0 <= index2₁₅
                  && index2₁₅ < nondet_short₁
                  && 0 <= index1₁₄
                  && index1₁₄ < nondet_short₁
                  && -32768 <= index2₁₅
                  && index2₁₅ < 32768
                  && -32768 <= index1₁₄
                  && index1₁₄ < 32768
                  && array₄₁[-1 + -index1₁₄ + nondet_short₁][index2₁₅] == (-1) * (-1) * (-1) * (-1))
          || (exists index1₁₄: int, index2₁₅: int, temp₂₁: int ::
                  (temp₂₁ == 0
                     ==> false)
                  && -2147483648 <= temp₂₁
                  && temp₂₁ < 2147483648
                  && (index1₁₄ == index2₁₅
                     ==> false)
                  && index1₁₄ == index2₁₅
                  && 0 <= index2₁₅
                  && index2₁₅ < nondet_short₁
                  && 0 <= index1₁₄
                  && index1₁₄ < nondet_short₁
                  && -32768 <= index2₁₅
                  && index2₁₅ < 32768
                  && -32768 <= index1₁₄
                  && index1₁₄ < 32768
                  && array₄₁[index1₁₄][index2₁₅] == -1)
          || (exists index1₁₄: int, index2₁₅: int, temp₂₂: int ::
                  (temp₂₂ == 0
                     ==> false)
                  && -2147483648 <= temp₂₂
                  && temp₂₂ < 2147483648
                  && (index1₁₄ == index2₁₅
                     ==> false)
                  && 0 <= index2₁₅
                  && index2₁₅ < nondet_short₁
                  && 0 <= index1₁₄
                  && index1₁₄ < nondet_short₁
                  && -32768 <= index2₁₅
                  && index2₁₅ < 32768
                  && -32768 <= index1₁₄
                  && index1₁₄ < 32768)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₄₁: [int][int]int, row₄₂: int, index1₁₄: int, index2₁₅: int, temp₁₉: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₄₂
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₄₂
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
                                || array₇[row₁₀][column₆] == array₄₁[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₁₉ == 0
        && -2147483648 <= temp₁₉
        && temp₁₉ < 2147483648
        && index1₁₄ == index2₁₅
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
        && -32768 <= index2₁₅
        && index2₁₅ < 32768
        && -32768 <= index1₁₄
        && index1₁₄ < 32768
         ==> row₄₂ < nondet_short₁));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₄₁: [int][int]int, row₄₂: int, index1₁₄: int, index2₁₅: int, temp₂₂: int ::
      (  -32768 <= nondet_short₁
        && nondet_short₁ < 32768
        && 0 < nondet_short₁
        && 0 <= row₄₂
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₄₂
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
                                || array₇[row₁₀][column₆] == array₄₁[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₂₂ == 0
        && -2147483648 <= temp₂₂
        && temp₂₂ < 2147483648
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
        && -32768 <= index2₁₅
        && index2₁₅ < 32768
        && -32768 <= index1₁₄
        && index1₁₄ < 32768
         ==> row₄₂ < nondet_short₁
          || index1₁₄ == index2₁₅));


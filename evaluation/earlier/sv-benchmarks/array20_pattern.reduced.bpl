data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₄₁: [int][int]int, row₄₂: int, array₁₁₇: [int][int]int, column₁₁₈: int, row₁₀: int ::
      (  0 < nondet_short₁
        && 0 <= row₄₂
        && (forall row₁₈₇: int ::
              (  0 <= row₁₈₇
                && row₁₈₇ < row₄₂
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> column₆ < nondet_short₁
                                  && array₇[row₁₈₇][column₆] == 0))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₁₈₇][column₆] == array₄₁[row₁₈₇][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₈₇ < nondet_short₁)))
        && row₄₂ < nondet_short₁
        && 0 <= column₁₁₈
        && (forall column₆: int ::
              (  0 <= column₆
                && column₆ < column₁₁₈
                 ==> column₆ < nondet_short₁
                  && array₁₁₇[row₄₂][column₆] == 0))
        && (forall column₆: int ::
                  0 <= column₆
                  && column₆ < column₁₁₈
                || array₁₁₇[row₄₂][column₆] == array₄₁[row₄₂][column₆])
        && 0 <= row₁₀
        && row₁₀ < row₄₂ + 1
         ==> column₁₁₈ < nondet_short₁
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
                          || array₇[row₁₀][column₆] == array₁₁₇[row₁₀][column₆])
                  && (column₈ < nondet_short₁
                     ==> false)
                  && row₁₀ < nondet_short₁)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₄₁: [int][int]int, row₄₂: int ::
      (  0 < nondet_short₁
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
          || (exists nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₁₉: int ::
                  (temp₁₉ == 0
                     ==> false)
                  && nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁
                  && 0 <= nondet_short₅₁₅
                  && nondet_short₅₁₅ < nondet_short₁
                  && 0 <= nondet_short₄₁₄
                  && nondet_short₄₁₄ < nondet_short₁
                  && array₄₁[-1 + -nondet_short₄₁₄ + nondet_short₁][nondet_short₅₁₅] == (-1) * (-1) * (-1) * (-1))
          || (exists nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₂₀: int ::
                  (temp₂₀ == 0
                     ==> false)
                  && nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁
                  && (nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁
                     ==> false)
                  && 0 <= nondet_short₅₁₅
                  && nondet_short₅₁₅ < nondet_short₁
                  && 0 <= nondet_short₄₁₄
                  && nondet_short₄₁₄ < nondet_short₁
                  && array₄₁[-1 + -nondet_short₄₁₄ + nondet_short₁][nondet_short₅₁₅] == (-1) * (-1) * (-1) * (-1))
          || (exists nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₂₁: int ::
                  (temp₂₁ == 0
                     ==> false)
                  && (nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁
                     ==> false)
                  && nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁
                  && 0 <= nondet_short₅₁₅
                  && nondet_short₅₁₅ < nondet_short₁
                  && 0 <= nondet_short₄₁₄
                  && nondet_short₄₁₄ < nondet_short₁
                  && array₄₁[nondet_short₄₁₄][nondet_short₅₁₅] == -1)
          || (exists nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₂₂: int ::
                  (temp₂₂ == 0
                     ==> false)
                  && (nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁
                     ==> false)
                  && 0 <= nondet_short₅₁₅
                  && nondet_short₅₁₅ < nondet_short₁
                  && 0 <= nondet_short₄₁₄
                  && nondet_short₄₁₄ < nondet_short₁)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₄₁: [int][int]int, row₄₂: int, nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₁₉: int ::
      (  0 < nondet_short₁
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
        && nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁
        && 0 <= nondet_short₅₁₅
        && nondet_short₅₁₅ < nondet_short₁
        && 0 <= nondet_short₄₁₄
        && nondet_short₄₁₄ < nondet_short₁
         ==> row₄₂ < nondet_short₁));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₄₁: [int][int]int, row₄₂: int, nondet_short₄₁₄: int, nondet_short₅₁₅: int, temp₂₂: int ::
      (  0 < nondet_short₁
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
        && 0 <= nondet_short₅₁₅
        && nondet_short₅₁₅ < nondet_short₁
        && 0 <= nondet_short₄₁₄
        && nondet_short₄₁₄ < nondet_short₁
         ==> row₄₂ < nondet_short₁
          || nondet_short₄₁₄ + nondet_short₅₁₅ == -1 + nondet_short₁));


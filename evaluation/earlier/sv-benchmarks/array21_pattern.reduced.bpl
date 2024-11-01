data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₄₆: [int][int]int, row₄₇: int, array₂₄₉: [int][int]int, column₂₅₀: int, row₁₀: int ::
      (  1 < nondet_short₁
        && 0 <= row₄₇
        && (forall row₃₁₉: int ::
              (  0 <= row₃₁₉
                && row₃₁₉ < row₄₇
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> column₆ < nondet_short₁
                                  && array₇[row₃₁₉][column₆] == 0))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₃₁₉][column₆] == array₄₆[row₃₁₉][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₃₁₉ < nondet_short₁)))
        && row₄₇ < nondet_short₁
        && 0 <= column₂₅₀
        && (forall column₆: int ::
              (  0 <= column₆
                && column₆ < column₂₅₀
                 ==> column₆ < nondet_short₁
                  && array₂₄₉[row₄₇][column₆] == 0))
        && (forall column₆: int ::
                  0 <= column₆
                  && column₆ < column₂₅₀
                || array₂₄₉[row₄₇][column₆] == array₄₆[row₄₇][column₆])
        && 0 <= row₁₀
        && row₁₀ < row₄₇ + 1
         ==> column₂₅₀ < nondet_short₁
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
                          || array₇[row₁₀][column₆] == array₂₄₉[row₁₀][column₆])
                  && (column₈ < nondet_short₁
                     ==> false)
                  && row₁₀ < nondet_short₁)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₄₆: [int][int]int, row₄₇: int, index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₅₂₁: int, temp₂₄: int ::
      (  1 < nondet_short₁
        && 0 <= row₄₇
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₄₇
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
                                || array₇[row₁₀][column₆] == array₄₆[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₂₄ == 0
        && outerBoundaryPatternCheck₄₁₈ == 0
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
         ==> row₄₇ < nondet_short₁
          || outerBoundaryPatternCheck₅₂₁ == 0));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₄₆: [int][int]int, row₄₇: int, index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, temp₂₅: int ::
      (  1 < nondet_short₁
        && 0 <= row₄₇
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₄₇
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
                                || array₇[row₁₀][column₆] == array₄₆[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₂₅ == 0
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
         ==> row₄₇ < nondet_short₁
          || outerBoundaryPatternCheck₄₁₈ == 0));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₄₆: [int][int]int, row₄₇: int, index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₅₂₁: int, temp₂₆: int ::
      (  1 < nondet_short₁
        && 0 <= row₄₇
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₄₇
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
                                || array₇[row₁₀][column₆] == array₄₆[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₂₆ == 0
        && outerBoundaryPatternCheck₅₂₁ == 0
        && outerBoundaryPatternCheck₄₁₈ == 0
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
         ==> row₄₇ < nondet_short₁));


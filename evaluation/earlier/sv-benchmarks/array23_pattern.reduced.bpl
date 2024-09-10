data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₅₀: [int][int]int, row₅₁: int, array₃₁₇: [int][int]int, column₃₁₈: int, row₁₀: int ::
      (  1 < nondet_short₁
        && 0 <= row₅₁
        && (forall row₃₈₇: int ::
              (  0 <= row₃₈₇
                && row₃₈₇ < row₅₁
                 ==> (exists array₇: [int][int]int, column₈: int ::
                        0 <= column₈
                        && (forall column₆: int ::
                              (  0 <= column₆
                                && column₆ < column₈
                                 ==> column₆ < nondet_short₁
                                  && array₇[row₃₈₇][column₆] == 0))
                        && (forall column₆: int ::
                                  0 <= column₆
                                  && column₆ < column₈
                                || array₇[row₃₈₇][column₆] == array₅₀[row₃₈₇][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₃₈₇ < nondet_short₁)))
        && row₅₁ < nondet_short₁
        && 0 <= column₃₁₈
        && (forall column₆: int ::
              (  0 <= column₆
                && column₆ < column₃₁₈
                 ==> column₆ < nondet_short₁
                  && array₃₁₇[row₅₁][column₆] == 0))
        && (forall column₆: int ::
                  0 <= column₆
                  && column₆ < column₃₁₈
                || array₃₁₇[row₅₁][column₆] == array₅₀[row₅₁][column₆])
        && 0 <= row₁₀
        && row₁₀ < row₅₁ + 1
         ==> column₃₁₈ < nondet_short₁
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
                          || array₇[row₁₀][column₆] == array₃₁₇[row₁₀][column₆])
                  && (column₈ < nondet_short₁
                     ==> false)
                  && row₁₀ < nondet_short₁)));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₅₀: [int][int]int, row₅₁: int, index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₆₂₃: int, temp₂₈: int ::
      (  1 < nondet_short₁
        && 0 <= row₅₁
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₅₁
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
                                || array₇[row₁₀][column₆] == array₅₀[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₂₈ == 0
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
         ==> row₅₁ < nondet_short₁
          || outerBoundaryPatternCheck₄₁₈ == 0
          || outerBoundaryPatternCheck₆₂₃ == 0));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₅₀: [int][int]int, row₅₁: int, index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₆₂₅: int, temp₂₉: int ::
      (  1 < nondet_short₁
        && 0 <= row₅₁
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₅₁
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
                                || array₇[row₁₀][column₆] == array₅₀[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₂₉ == 0
        && outerBoundaryPatternCheck₄₁₈ == 0
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
         ==> row₅₁ < nondet_short₁
          || outerBoundaryPatternCheck₆₂₅ == 0));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₅₀: [int][int]int, row₅₁: int, index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₆₂₃: int, temp₃₀: int ::
      (  1 < nondet_short₁
        && 0 <= row₅₁
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₅₁
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
                                || array₇[row₁₀][column₆] == array₅₀[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₃₀ == 0
        && outerBoundaryPatternCheck₆₂₃ == 0
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
         ==> row₅₁ < nondet_short₁
          || outerBoundaryPatternCheck₄₁₈ == 0));

goal {:named "invariant entry"} (forall nondet_short₁: int, array₅₀: [int][int]int, row₅₁: int, index1₁₄: int, index2₁₅: int, outerBoundaryPatternCheck₄₁₈: int, outerBoundaryPatternCheck₆₂₅: int, temp₃₁: int ::
      (  1 < nondet_short₁
        && 0 <= row₅₁
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₅₁
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
                                || array₇[row₁₀][column₆] == array₅₀[row₁₀][column₆])
                        && (column₈ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && temp₃₁ == 0
        && outerBoundaryPatternCheck₆₂₅ == 0
        && outerBoundaryPatternCheck₄₁₈ == 0
        && 0 <= index2₁₅
        && index2₁₅ < nondet_short₁
        && 0 <= index1₁₄
        && index1₁₄ < nondet_short₁
         ==> row₅₁ < nondet_short₁));


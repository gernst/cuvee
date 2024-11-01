data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₂₂: [int][int]int, row₂₃: int, array₃₄: [int][int]int, column₃₅: int, row₇: int ::
      (  1 < nondet_short₁
        && 0 <= row₂₃
        && (forall row₂₃₆: int ::
              (  0 <= row₂₃₆
                && row₂₃₆ < row₂₃
                 ==> (exists array₄: [int][int]int, column₅: int ::
                        0 <= column₅
                        && (forall column₃: int ::
                              (  0 <= column₃
                                && column₃ < column₅
                                 ==> row₂₃₆ % 2 == 0
                                    && column₃ % 2 == 0
                                    && column₃ < nondet_short₁
                                    && array₄[row₂₃₆][column₃] == (-1) * (-1)
                                  ||   row₂₃₆ % 2 == 1
                                    && column₃ % 2 == 1
                                    && (  row₂₃₆ % 2 == 0
                                      && column₃ % 2 == 0
                                       ==> false)
                                    && column₃ < nondet_short₁
                                    && array₄[row₂₃₆][column₃] == -1
                                  ||   (  row₂₃₆ % 2 == 1
                                      && column₃ % 2 == 1
                                       ==> false)
                                    && (  row₂₃₆ % 2 == 0
                                      && column₃ % 2 == 0
                                       ==> false)
                                    && column₃ < nondet_short₁
                                    && array₄[row₂₃₆][column₃] == 0))
                        && (forall column₃: int ::
                                  0 <= column₃
                                  && column₃ < column₅
                                || array₄[row₂₃₆][column₃] == array₂₂[row₂₃₆][column₃])
                        && (column₅ < nondet_short₁
                           ==> false)
                        && row₂₃₆ < nondet_short₁)))
        && row₂₃ < nondet_short₁
        && 0 <= column₃₅
        && (forall column₃: int ::
              (  0 <= column₃
                && column₃ < column₃₅
                 ==> row₂₃ % 2 == 0
                    && column₃ % 2 == 0
                    && column₃ < nondet_short₁
                    && array₃₄[row₂₃][column₃] == (-1) * (-1)
                  ||   row₂₃ % 2 == 1
                    && column₃ % 2 == 1
                    && (  row₂₃ % 2 == 0
                      && column₃ % 2 == 0
                       ==> false)
                    && column₃ < nondet_short₁
                    && array₃₄[row₂₃][column₃] == -1
                  ||   (  row₂₃ % 2 == 1
                      && column₃ % 2 == 1
                       ==> false)
                    && (  row₂₃ % 2 == 0
                      && column₃ % 2 == 0
                       ==> false)
                    && column₃ < nondet_short₁
                    && array₃₄[row₂₃][column₃] == 0))
        && (forall column₃: int ::
                  0 <= column₃
                  && column₃ < column₃₅
                || array₃₄[row₂₃][column₃] == array₂₂[row₂₃][column₃])
        && 0 <= row₇
        && row₇ < row₂₃ + 1
         ==> column₃₅ < nondet_short₁
          || (exists array₄: [int][int]int, column₅: int ::
                  0 <= column₅
                  && (forall column₃: int ::
                        (  0 <= column₃
                          && column₃ < column₅
                           ==> row₇ % 2 == 0
                              && column₃ % 2 == 0
                              && column₃ < nondet_short₁
                              && array₄[row₇][column₃] == (-1) * (-1)
                            ||   row₇ % 2 == 1
                              && column₃ % 2 == 1
                              && (  row₇ % 2 == 0
                                && column₃ % 2 == 0
                                 ==> false)
                              && column₃ < nondet_short₁
                              && array₄[row₇][column₃] == -1
                            ||   (  row₇ % 2 == 1
                                && column₃ % 2 == 1
                                 ==> false)
                              && (  row₇ % 2 == 0
                                && column₃ % 2 == 0
                                 ==> false)
                              && column₃ < nondet_short₁
                              && array₄[row₇][column₃] == 0))
                  && (forall column₃: int ::
                            0 <= column₃
                            && column₃ < column₅
                          || array₄[row₇][column₃] == array₃₄[row₇][column₃])
                  && (column₅ < nondet_short₁
                     ==> false)
                  && row₇ < nondet_short₁)));

goal {:named "assert"} (forall nondet_short₁: int, array₂₂: [int][int]int, row₂₃: int, sum₂₅: int, row₂₆: int ::
      (  1 < nondet_short₁
        && 0 <= row₂₃
        && (forall row₇: int ::
              (  0 <= row₇
                && row₇ < row₂₃
                 ==> (exists array₄: [int][int]int, column₅: int ::
                        0 <= column₅
                        && (forall column₃: int ::
                              (  0 <= column₃
                                && column₃ < column₅
                                 ==> row₇ % 2 == 0
                                    && column₃ % 2 == 0
                                    && column₃ < nondet_short₁
                                    && array₄[row₇][column₃] == (-1) * (-1)
                                  ||   row₇ % 2 == 1
                                    && column₃ % 2 == 1
                                    && (  row₇ % 2 == 0
                                      && column₃ % 2 == 0
                                       ==> false)
                                    && column₃ < nondet_short₁
                                    && array₄[row₇][column₃] == -1
                                  ||   (  row₇ % 2 == 1
                                      && column₃ % 2 == 1
                                       ==> false)
                                    && (  row₇ % 2 == 0
                                      && column₃ % 2 == 0
                                       ==> false)
                                    && column₃ < nondet_short₁
                                    && array₄[row₇][column₃] == 0))
                        && (forall column₃: int ::
                                  0 <= column₃
                                  && column₃ < column₅
                                || array₄[row₇][column₃] == array₂₂[row₇][column₃])
                        && (column₅ < nondet_short₁
                           ==> false)
                        && row₇ < nondet_short₁)))
        && 0 <= row₂₆
        && (forall row₁₇: int ::
              (  0 <= row₁₇
                && row₁₇ < row₂₆
                 ==> (exists column₁₄: int ::
                        0 <= column₁₄
                        && (forall column₁₂: int ::
                              (  0 <= column₁₂
                                && column₁₂ < column₁₄
                                 ==> column₁₂ < nondet_short₁))
                        && (column₁₄ < nondet_short₁
                           ==> false)
                        && row₁₇ < nondet_short₁)))
         ==> row₂₆ < nondet_short₁
          || row₂₃ < nondet_short₁
          || sum₂₅ == 0
          || sum₂₅ == nondet_short₁));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₂₂: [int][int]int, row₂₃: int, array₃₄: [int][int]int, column₃₅: int, column₃: int ::
      (  0 < nondet_short₁
        && 0 <= row₂₃
        && (forall row₇: int ::
              (  0 <= row₇
                && row₇ < row₂₃
                 ==> (exists array₄: [int][int]int, column₅: int ::
                        0 <= column₅
                        && (forall column₈₇: int ::
                              (  0 <= column₈₇
                                && column₈₇ < column₅
                                 ==> row₇ == column₈₇
                                    && column₈₇ < nondet_short₁
                                    && array₄[row₇][row₇] == 0
                                  ||   (row₇ == column₈₇
                                       ==> false)
                                    && column₈₇ < nondet_short₁
                                    && array₄[row₇][column₈₇] == row₇))
                        && (forall column₈₈: int ::
                                  0 <= column₈₈
                                  && column₈₈ < column₅
                                ||   array₄[row₇][row₇] == array₂₂[row₇][row₇]
                                  && array₄[row₇][column₈₈] == array₂₂[row₇][column₈₈])
                        && (column₅ < nondet_short₁
                           ==> false)
                        && row₇ < nondet_short₁)))
        && row₂₃ < nondet_short₁
        && 0 <= column₃₅
        && (forall column₈₉: int ::
              (  0 <= column₈₉
                && column₈₉ < column₃₅
                 ==> row₂₃ == column₈₉
                    && column₈₉ < nondet_short₁
                    && array₃₄[row₂₃][row₂₃] == 0
                  ||   (row₂₃ == column₈₉
                       ==> false)
                    && column₈₉ < nondet_short₁
                    && array₃₄[row₂₃][column₈₉] == row₂₃))
        && (forall column₉₀: int ::
                  0 <= column₉₀
                  && column₉₀ < column₃₅
                ||   array₃₄[row₂₃][row₂₃] == array₂₂[row₂₃][row₂₃]
                  && array₃₄[row₂₃][column₉₀] == array₂₂[row₂₃][column₉₀])
        && column₃₅ < nondet_short₁
        && row₂₃ == column₃₅
         ==> 0 <= column₃
          || array₃₄[row₂₃ := array₃₄[row₂₃][row₂₃ := 0]][row₂₃][row₂₃] == array₂₂[row₂₃][row₂₃]));

goal {:named "invariant forward"} (forall nondet_short₁: int, array₂₂: [int][int]int, row₂₃: int, array₃₄: [int][int]int, column₃₅: int, column₃: int ::
      (  0 < nondet_short₁
        && 0 <= row₂₃
        && (forall row₇: int ::
              (  0 <= row₇
                && row₇ < row₂₃
                 ==> (exists array₄: [int][int]int, column₅: int ::
                        0 <= column₅
                        && (forall column₁₀₃: int ::
                              (  0 <= column₁₀₃
                                && column₁₀₃ < column₅
                                 ==> row₇ == column₁₀₃
                                    && column₁₀₃ < nondet_short₁
                                    && array₄[row₇][row₇] == 0
                                  ||   (row₇ == column₁₀₃
                                       ==> false)
                                    && column₁₀₃ < nondet_short₁
                                    && array₄[row₇][column₁₀₃] == row₇))
                        && (forall column₁₀₄: int ::
                                  0 <= column₁₀₄
                                  && column₁₀₄ < column₅
                                ||   array₄[row₇][row₇] == array₂₂[row₇][row₇]
                                  && array₄[row₇][column₁₀₄] == array₂₂[row₇][column₁₀₄])
                        && (column₅ < nondet_short₁
                           ==> false)
                        && row₇ < nondet_short₁)))
        && row₂₃ < nondet_short₁
        && 0 <= column₃₅
        && (forall column₁₀₅: int ::
              (  0 <= column₁₀₅
                && column₁₀₅ < column₃₅
                 ==> row₂₃ == column₁₀₅
                    && column₁₀₅ < nondet_short₁
                    && array₃₄[row₂₃][row₂₃] == 0
                  ||   (row₂₃ == column₁₀₅
                       ==> false)
                    && column₁₀₅ < nondet_short₁
                    && array₃₄[row₂₃][column₁₀₅] == row₂₃))
        && (forall column₁₀₆: int ::
                  0 <= column₁₀₆
                  && column₁₀₆ < column₃₅
                ||   array₃₄[row₂₃][row₂₃] == array₂₂[row₂₃][row₂₃]
                  && array₃₄[row₂₃][column₁₀₆] == array₂₂[row₂₃][column₁₀₆])
        && column₃₅ < nondet_short₁
        && row₂₃ == column₃₅
         ==> column₃ < column₃₅ + 1
          || array₃₄[row₂₃ := array₃₄[row₂₃][row₂₃ := 0]][row₂₃][row₂₃] == array₂₂[row₂₃][row₂₃]));

goal {:named "invariant forward"} (forall nondet_short₁: int, array₂₂: [int][int]int, row₂₃: int, array₃₄: [int][int]int, column₃₅: int, row₇: int ::
      (  0 < nondet_short₁
        && 0 <= row₂₃
        && (forall row₁₅₉: int ::
              (  0 <= row₁₅₉
                && row₁₅₉ < row₂₃
                 ==> (exists array₄: [int][int]int, column₅: int ::
                        0 <= column₅
                        && (forall column₃: int ::
                              (  0 <= column₃
                                && column₃ < column₅
                                 ==> row₁₅₉ == column₃
                                    && column₃ < nondet_short₁
                                    && array₄[row₁₅₉][row₁₅₉] == 0
                                  ||   (row₁₅₉ == column₃
                                       ==> false)
                                    && column₃ < nondet_short₁
                                    && array₄[row₁₅₉][column₃] == row₁₅₉))
                        && (forall column₃: int ::
                                  0 <= column₃
                                  && column₃ < column₅
                                ||   array₄[row₁₅₉][row₁₅₉] == array₂₂[row₁₅₉][row₁₅₉]
                                  && array₄[row₁₅₉][column₃] == array₂₂[row₁₅₉][column₃])
                        && (column₅ < nondet_short₁
                           ==> false)
                        && row₁₅₉ < nondet_short₁)))
        && row₂₃ < nondet_short₁
        && 0 <= column₃₅
        && (forall column₃: int ::
              (  0 <= column₃
                && column₃ < column₃₅
                 ==> row₂₃ == column₃
                    && column₃ < nondet_short₁
                    && array₃₄[row₂₃][row₂₃] == 0
                  ||   (row₂₃ == column₃
                       ==> false)
                    && column₃ < nondet_short₁
                    && array₃₄[row₂₃][column₃] == row₂₃))
        && (forall column₃: int ::
                  0 <= column₃
                  && column₃ < column₃₅
                ||   array₃₄[row₂₃][row₂₃] == array₂₂[row₂₃][row₂₃]
                  && array₃₄[row₂₃][column₃] == array₂₂[row₂₃][column₃])
        && 0 <= row₇
        && row₇ < row₂₃ + 1
         ==> column₃₅ < nondet_short₁
          || (exists array₄: [int][int]int, column₅: int ::
                  0 <= column₅
                  && (forall column₃: int ::
                        (  0 <= column₃
                          && column₃ < column₅
                           ==> row₇ == column₃
                              && column₃ < nondet_short₁
                              && array₄[row₇][row₇] == 0
                            ||   (row₇ == column₃
                                 ==> false)
                              && column₃ < nondet_short₁
                              && array₄[row₇][column₃] == row₇))
                  && (forall column₃: int ::
                            0 <= column₃
                            && column₃ < column₅
                          ||   array₄[row₇][row₇] == array₃₄[row₇][row₇]
                            && array₄[row₇][column₃] == array₃₄[row₇][column₃])
                  && (column₅ < nondet_short₁
                     ==> false)
                  && row₇ < nondet_short₁)));

goal {:named "assert"} (forall nondet_short₁: int, array₂₂: [int][int]int, row₂₃: int, sum₂₅: int, row₂₆: int ::
      (  0 < nondet_short₁
        && 0 <= row₂₃
        && (forall row₇: int ::
              (  0 <= row₇
                && row₇ < row₂₃
                 ==> (exists array₄: [int][int]int, column₅: int ::
                        0 <= column₅
                        && (forall column₃: int ::
                              (  0 <= column₃
                                && column₃ < column₅
                                 ==> row₇ == column₃
                                    && column₃ < nondet_short₁
                                    && array₄[row₇][row₇] == 0
                                  ||   (row₇ == column₃
                                       ==> false)
                                    && column₃ < nondet_short₁
                                    && array₄[row₇][column₃] == row₇))
                        && (forall column₃: int ::
                                  0 <= column₃
                                  && column₃ < column₅
                                ||   array₄[row₇][row₇] == array₂₂[row₇][row₇]
                                  && array₄[row₇][column₃] == array₂₂[row₇][column₃])
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
          || 2 * sum₂₅ == nondet_short₁ * (nondet_short₁ - 1) * (nondet_short₁ - 1)));


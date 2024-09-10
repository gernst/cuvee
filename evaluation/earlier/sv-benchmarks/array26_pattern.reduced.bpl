data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall nondet_short₁: int, array₂₆: [int][int]int, row₂₈: int, array₃₉: [int][int]int, value₄₀: int, column₄₁: int, value₃: int, column₄: int ::
      (  1 < nondet_short₁
        && 0 <= row₂₈
        && (forall row₁₀: int ::
              (  0 <= row₁₀
                && row₁₀ < row₂₈
                 ==> (exists array₅: [int][int]int, column₇: int ::
                        0 <= column₇
                        && (forall value₈₈: int, column₈₉: int ::
                              (  0 <= column₈₉
                                && column₈₉ < column₇
                                 ==> row₁₀ % 2 == 0
                                    && column₈₉ % 2 == 0
                                    && column₈₉ < nondet_short₁
                                    && array₅[row₁₀][column₈₉] == value₈₈
                                  ||   row₁₀ % 2 == 1
                                    && column₈₉ % 2 == 1
                                    && (  row₁₀ % 2 == 0
                                      && column₈₉ % 2 == 0
                                       ==> false)
                                    && column₈₉ < nondet_short₁
                                    && array₅[row₁₀][column₈₉] == value₈₈
                                  ||   (  row₁₀ % 2 == 1
                                      && column₈₉ % 2 == 1
                                       ==> false)
                                    && (  row₁₀ % 2 == 0
                                      && column₈₉ % 2 == 0
                                       ==> false)
                                    && column₈₉ < nondet_short₁
                                    && array₅[row₁₀][column₈₉] == 0))
                        && (forall column₉₀: int ::
                                  0 <= column₉₀
                                  && column₉₀ < column₇
                                || array₅[row₁₀][column₉₀] == array₂₆[row₁₀][column₉₀])
                        && (column₇ < nondet_short₁
                           ==> false)
                        && row₁₀ < nondet_short₁)))
        && row₂₈ < nondet_short₁
        && 0 <= column₄₁
        && (forall value₉₁: int, column₉₂: int ::
              (  0 <= column₉₂
                && column₉₂ < column₄₁
                 ==> row₂₈ % 2 == 0
                    && column₉₂ % 2 == 0
                    && column₉₂ < nondet_short₁
                    && array₃₉[row₂₈][column₉₂] == value₉₁
                  ||   row₂₈ % 2 == 1
                    && column₉₂ % 2 == 1
                    && (  row₂₈ % 2 == 0
                      && column₉₂ % 2 == 0
                       ==> false)
                    && column₉₂ < nondet_short₁
                    && array₃₉[row₂₈][column₉₂] == value₉₁
                  ||   (  row₂₈ % 2 == 1
                      && column₉₂ % 2 == 1
                       ==> false)
                    && (  row₂₈ % 2 == 0
                      && column₉₂ % 2 == 0
                       ==> false)
                    && column₉₂ < nondet_short₁
                    && array₃₉[row₂₈][column₉₂] == 0))
        && (forall column₉₃: int ::
                  0 <= column₉₃
                  && column₉₃ < column₄₁
                || array₃₉[row₂₈][column₉₃] == array₂₆[row₂₈][column₉₃])
        && column₄₁ < nondet_short₁
        && row₂₈ % 2 == 0
        && column₄₁ % 2 == 0
        && 0 <= column₄
        && column₄ < column₄₁ + 1
         ==> row₂₈ % 2 == 0
            && column₄ % 2 == 0
            && column₄ < nondet_short₁
            && array₃₉[row₂₈ := array₃₉[row₂₈][column₄₁ := value₄₀]][row₂₈][column₄] == value₃
          ||   row₂₈ % 2 == 1
            && column₄ % 2 == 1
            && (  row₂₈ % 2 == 0
              && column₄ % 2 == 0
               ==> false)
            && column₄ < nondet_short₁
            && array₃₉[row₂₈ := array₃₉[row₂₈][column₄₁ := value₄₀]][row₂₈][column₄] == value₃
          ||   (  row₂₈ % 2 == 1
              && column₄ % 2 == 1
               ==> false)
            && (  row₂₈ % 2 == 0
              && column₄ % 2 == 0
               ==> false)
            && column₄ < nondet_short₁
            && array₃₉[row₂₈ := array₃₉[row₂₈][column₄₁ := value₄₀]][row₂₈][column₄] == 0));

goal {:named "invariant forward"} (forall nondet_short₁: int, array₂₆: [int][int]int, row₂₈: int, array₃₉: [int][int]int, column₄₁: int, row₁₀: int ::
      (  1 < nondet_short₁
        && 0 <= row₂₈
        && (forall row₂₆₉: int ::
              (  0 <= row₂₆₉
                && row₂₆₉ < row₂₈
                 ==> (exists array₅: [int][int]int, column₇: int ::
                        0 <= column₇
                        && (forall value₃: int, column₄: int ::
                              (  0 <= column₄
                                && column₄ < column₇
                                 ==> row₂₆₉ % 2 == 0
                                    && column₄ % 2 == 0
                                    && column₄ < nondet_short₁
                                    && array₅[row₂₆₉][column₄] == value₃
                                  ||   row₂₆₉ % 2 == 1
                                    && column₄ % 2 == 1
                                    && (  row₂₆₉ % 2 == 0
                                      && column₄ % 2 == 0
                                       ==> false)
                                    && column₄ < nondet_short₁
                                    && array₅[row₂₆₉][column₄] == value₃
                                  ||   (  row₂₆₉ % 2 == 1
                                      && column₄ % 2 == 1
                                       ==> false)
                                    && (  row₂₆₉ % 2 == 0
                                      && column₄ % 2 == 0
                                       ==> false)
                                    && column₄ < nondet_short₁
                                    && array₅[row₂₆₉][column₄] == 0))
                        && (forall column₄: int ::
                                  0 <= column₄
                                  && column₄ < column₇
                                || array₅[row₂₆₉][column₄] == array₂₆[row₂₆₉][column₄])
                        && (column₇ < nondet_short₁
                           ==> false)
                        && row₂₆₉ < nondet_short₁)))
        && row₂₈ < nondet_short₁
        && 0 <= column₄₁
        && (forall value₃: int, column₄: int ::
              (  0 <= column₄
                && column₄ < column₄₁
                 ==> row₂₈ % 2 == 0
                    && column₄ % 2 == 0
                    && column₄ < nondet_short₁
                    && array₃₉[row₂₈][column₄] == value₃
                  ||   row₂₈ % 2 == 1
                    && column₄ % 2 == 1
                    && (  row₂₈ % 2 == 0
                      && column₄ % 2 == 0
                       ==> false)
                    && column₄ < nondet_short₁
                    && array₃₉[row₂₈][column₄] == value₃
                  ||   (  row₂₈ % 2 == 1
                      && column₄ % 2 == 1
                       ==> false)
                    && (  row₂₈ % 2 == 0
                      && column₄ % 2 == 0
                       ==> false)
                    && column₄ < nondet_short₁
                    && array₃₉[row₂₈][column₄] == 0))
        && (forall column₄: int ::
                  0 <= column₄
                  && column₄ < column₄₁
                || array₃₉[row₂₈][column₄] == array₂₆[row₂₈][column₄])
        && 0 <= row₁₀
        && row₁₀ < row₂₈ + 1
         ==> column₄₁ < nondet_short₁
          || (exists array₅: [int][int]int, column₇: int ::
                  0 <= column₇
                  && (forall value₃: int, column₄: int ::
                        (  0 <= column₄
                          && column₄ < column₇
                           ==> row₁₀ % 2 == 0
                              && column₄ % 2 == 0
                              && column₄ < nondet_short₁
                              && array₅[row₁₀][column₄] == value₃
                            ||   row₁₀ % 2 == 1
                              && column₄ % 2 == 1
                              && (  row₁₀ % 2 == 0
                                && column₄ % 2 == 0
                                 ==> false)
                              && column₄ < nondet_short₁
                              && array₅[row₁₀][column₄] == value₃
                            ||   (  row₁₀ % 2 == 1
                                && column₄ % 2 == 1
                                 ==> false)
                              && (  row₁₀ % 2 == 0
                                && column₄ % 2 == 0
                                 ==> false)
                              && column₄ < nondet_short₁
                              && array₅[row₁₀][column₄] == 0))
                  && (forall column₄: int ::
                            0 <= column₄
                            && column₄ < column₇
                          || array₅[row₁₀][column₄] == array₃₉[row₁₀][column₄])
                  && (column₇ < nondet_short₁
                     ==> false)
                  && row₁₀ < nondet_short₁)));


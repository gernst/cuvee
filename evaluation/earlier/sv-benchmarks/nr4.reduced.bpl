data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall CELLCOUNT₁₅: int, volArray₁₇: [int]int, i₁₈: int, volArray₂₁: [int]int, j₂₂: int, i₉: int ::
      (  -2147483648 <= CELLCOUNT₁₅
        && CELLCOUNT₁₅ < 2147483648
        && 1 < CELLCOUNT₁₅
        && CELLCOUNT₁₅ % 4 == 0
        && CELLCOUNT₁₅ % 4 == 0
        && 1 <= i₁₈
        && (forall i₁₀₆: int ::
              (  1 <= i₁₀₆
                && i₁₀₆ < i₁₈
                 ==> (exists volArray₆: [int]int, j₇: int ::
                        j₇ <= 4
                        && (forall j₅: int ::
                              (  j₇ < j₅
                                && j₅ <= 4
                                 ==> 2 <= j₅
                                    && 1 <= j₅
                                    && volArray₆[4 * i₁₀₆ + -j₅] == j₅
                                  ||   (2 <= j₅
                                       ==> false)
                                    && 1 <= j₅
                                    && volArray₆[4 * i₁₀₆ + -j₅] == 0))
                        && (forall j₅: int ::
                                  j₇ < j₅
                                  && j₅ <= 4
                                || volArray₆[4 * i₁₀₆ + -j₅] == volArray₁₇[4 * i₁₀₆ + -j₅])
                        && (1 <= j₇
                           ==> false)
                        && i₁₀₆ <= CELLCOUNT₁₅ / 4)))
        && i₁₈ <= CELLCOUNT₁₅ / 4
        && j₂₂ <= 4
        && (forall j₅: int ::
              (  j₂₂ < j₅
                && j₅ <= 4
                 ==> 2 <= j₅
                    && 1 <= j₅
                    && volArray₂₁[4 * i₁₈ + -j₅] == j₅
                  ||   (2 <= j₅
                       ==> false)
                    && 1 <= j₅
                    && volArray₂₁[4 * i₁₈ + -j₅] == 0))
        && (forall j₅: int ::
                  j₂₂ < j₅
                  && j₅ <= 4
                || volArray₂₁[4 * i₁₈ + -j₅] == volArray₁₇[4 * i₁₈ + -j₅])
        && 1 <= i₉
        && i₉ < i₁₈ + 1
         ==> 1 <= j₂₂
          || (exists volArray₆: [int]int, j₇: int ::
                  j₇ <= 4
                  && (forall j₅: int ::
                        (  j₇ < j₅
                          && j₅ <= 4
                           ==> 2 <= j₅
                              && 1 <= j₅
                              && volArray₆[4 * i₉ + -j₅] == j₅
                            ||   (2 <= j₅
                                 ==> false)
                              && 1 <= j₅
                              && volArray₆[4 * i₉ + -j₅] == 0))
                  && (forall j₅: int ::
                            j₇ < j₅
                            && j₅ <= 4
                          || volArray₆[4 * i₉ + -j₅] == volArray₂₁[4 * i₉ + -j₅])
                  && (1 <= j₇
                     ==> false)
                  && i₉ <= CELLCOUNT₁₅ / 4)));

goal {:named "assert"} (forall CELLCOUNT₁₅: int, volArray₁₇: [int]int, i₁₈: int, i₁₉: int ::
      (  -2147483648 <= CELLCOUNT₁₅
        && CELLCOUNT₁₅ < 2147483648
        && 1 < CELLCOUNT₁₅
        && CELLCOUNT₁₅ % 4 == 0
        && CELLCOUNT₁₅ % 4 == 0
        && 1 <= i₁₈
        && (forall i₉: int ::
              (  1 <= i₉
                && i₉ < i₁₈
                 ==> (exists volArray₆: [int]int, j₇: int ::
                        j₇ <= 4
                        && (forall j₅: int ::
                              (  j₇ < j₅
                                && j₅ <= 4
                                 ==> 2 <= j₅
                                    && 1 <= j₅
                                    && volArray₆[4 * i₉ + -j₅] == j₅
                                  ||   (2 <= j₅
                                       ==> false)
                                    && 1 <= j₅
                                    && volArray₆[4 * i₉ + -j₅] == 0))
                        && (forall j₅: int ::
                                  j₇ < j₅
                                  && j₅ <= 4
                                || volArray₆[4 * i₉ + -j₅] == volArray₁₇[4 * i₉ + -j₅])
                        && (1 <= j₇
                           ==> false)
                        && i₉ <= CELLCOUNT₁₅ / 4)))
        && 0 <= i₁₉
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₁₉
                 ==> i₁₃ < CELLCOUNT₁₅))
        && i₁₉ < CELLCOUNT₁₅
         ==> i₁₈ <= CELLCOUNT₁₅ / 4
          || 2 <= volArray₁₇[i₁₉]
          || volArray₁₇[i₁₉] == 0));


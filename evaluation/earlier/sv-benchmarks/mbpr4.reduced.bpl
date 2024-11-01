data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall CELLCOUNT₁₈: int, volArray: [int]int, volArray₁₉: [int]int, i₂₀: int, volArray₂₁: [int]int, i₂₂: int, volArray₂₃: [int]int, i₂₄: int, volArray₂₅: [int]int, i₂₆: int, i₂₇: int ::
      (  1 < CELLCOUNT₁₈
        && CELLCOUNT₁₈ % 4 == 0
        && CELLCOUNT₁₈ % 4 == 0
        && 1 <= i₂₀
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₂₀
                 ==> 2 <= 5
                    && i₄ <= CELLCOUNT₁₈ / 4
                    && volArray₁₉[-4 + 4 * i₄] == 5
                  ||   (2 <= 5
                       ==> false)
                    && i₄ <= CELLCOUNT₁₈ / 4
                    && volArray₁₉[-4 + 4 * i₄] == 0))
        && (forall i₄: int ::
                  1 <= i₄
                  && i₄ < i₂₀
                || volArray₁₉[-4 + 4 * i₄] == volArray[-4 + 4 * i₄])
        && 1 <= i₂₂
        && (forall i₇: int ::
              (  1 <= i₇
                && i₇ < i₂₂
                 ==> 2 <= 7
                    && i₇ <= CELLCOUNT₁₈ / 4
                    && volArray₂₁[-3 + 4 * i₇] == 7
                  ||   (2 <= 7
                       ==> false)
                    && i₇ <= CELLCOUNT₁₈ / 4
                    && volArray₂₁[-3 + 4 * i₇] == 0))
        && (forall i₇: int ::
                  1 <= i₇
                  && i₇ < i₂₂
                || volArray₂₁[-3 + 4 * i₇] == volArray₁₉[-3 + 4 * i₇])
        && 1 <= i₂₄
        && (forall i₁₀: int ::
              (  1 <= i₁₀
                && i₁₀ < i₂₄
                 ==> 2 <= 3
                    && i₁₀ <= CELLCOUNT₁₈ / 4
                    && volArray₂₃[-2 + 4 * i₁₀] == 3
                  ||   (2 <= 3
                       ==> false)
                    && i₁₀ <= CELLCOUNT₁₈ / 4
                    && volArray₂₃[-2 + 4 * i₁₀] == 0))
        && (forall i₁₀: int ::
                  1 <= i₁₀
                  && i₁₀ < i₂₄
                || volArray₂₃[-2 + 4 * i₁₀] == volArray₂₁[-2 + 4 * i₁₀])
        && 1 <= i₂₆
        && (forall i₁₃: int ::
              (  1 <= i₁₃
                && i₁₃ < i₂₆
                 ==> 2 <= 1
                    && i₁₃ <= CELLCOUNT₁₈ / 4
                    && volArray₂₅[-1 + 4 * i₁₃] == 1
                  ||   (2 <= 1
                       ==> false)
                    && i₁₃ <= CELLCOUNT₁₈ / 4
                    && volArray₂₅[-1 + 4 * i₁₃] == 0))
        && (forall i₁₃: int ::
                  1 <= i₁₃
                  && i₁₃ < i₂₆
                || volArray₂₅[-1 + 4 * i₁₃] == volArray₂₃[-1 + 4 * i₁₃])
        && 0 <= i₂₇
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₂₇
                 ==> i₁₆ < CELLCOUNT₁₈))
        && i₂₇ < CELLCOUNT₁₈
         ==> i₂₆ <= CELLCOUNT₁₈ / 4
          || i₂₄ <= CELLCOUNT₁₈ / 4
          || i₂₂ <= CELLCOUNT₁₈ / 4
          || i₂₀ <= CELLCOUNT₁₈ / 4
          || 2 <= volArray₂₅[i₂₇]
          || volArray₂₅[i₂₇] == 0));


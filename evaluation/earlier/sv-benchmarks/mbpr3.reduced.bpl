data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall CELLCOUNT₁₅: int, volArray: [int]int, volArray₁₆: [int]int, i₁₇: int, volArray₁₈: [int]int, i₁₉: int, volArray₂₀: [int]int, i₂₁: int, i₂₂: int ::
      (  1 < CELLCOUNT₁₅
        && CELLCOUNT₁₅ % 3 == 0
        && CELLCOUNT₁₅ % 3 == 0
        && 1 <= i₁₇
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₁₇
                 ==> 2 <= 7
                    && i₄ <= CELLCOUNT₁₅ / 3
                    && volArray₁₆[-3 + 3 * i₄] == 7
                  ||   (2 <= 7
                       ==> false)
                    && i₄ <= CELLCOUNT₁₅ / 3
                    && volArray₁₆[-3 + 3 * i₄] == 0))
        && (forall i₄: int ::
                  1 <= i₄
                  && i₄ < i₁₇
                || volArray₁₆[-3 + 3 * i₄] == volArray[-3 + 3 * i₄])
        && 1 <= i₁₉
        && (forall i₇: int ::
              (  1 <= i₇
                && i₇ < i₁₉
                 ==> 2 <= 3
                    && i₇ <= CELLCOUNT₁₅ / 3
                    && volArray₁₈[-2 + 3 * i₇] == 3
                  ||   (2 <= 3
                       ==> false)
                    && i₇ <= CELLCOUNT₁₅ / 3
                    && volArray₁₈[-2 + 3 * i₇] == 0))
        && (forall i₇: int ::
                  1 <= i₇
                  && i₇ < i₁₉
                || volArray₁₈[-2 + 3 * i₇] == volArray₁₆[-2 + 3 * i₇])
        && 1 <= i₂₁
        && (forall i₁₀: int ::
              (  1 <= i₁₀
                && i₁₀ < i₂₁
                 ==> 2 <= 1
                    && i₁₀ <= CELLCOUNT₁₅ / 3
                    && volArray₂₀[-1 + 3 * i₁₀] == 1
                  ||   (2 <= 1
                       ==> false)
                    && i₁₀ <= CELLCOUNT₁₅ / 3
                    && volArray₂₀[-1 + 3 * i₁₀] == 0))
        && (forall i₁₀: int ::
                  1 <= i₁₀
                  && i₁₀ < i₂₁
                || volArray₂₀[-1 + 3 * i₁₀] == volArray₁₈[-1 + 3 * i₁₀])
        && 0 <= i₂₂
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₂
                 ==> i₁₃ < CELLCOUNT₁₅))
        && i₂₂ < CELLCOUNT₁₅
         ==> i₂₁ <= CELLCOUNT₁₅ / 3
          || i₁₉ <= CELLCOUNT₁₅ / 3
          || i₁₇ <= CELLCOUNT₁₅ / 3
          || 2 <= volArray₂₀[i₂₂]
          || volArray₂₀[i₂₂] == 0));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall CELLCOUNT₂₁: int, volArray: [int]int, volArray₂₂: [int]int, i₂₃: int, volArray₂₄: [int]int, i₂₅: int, volArray₂₆: [int]int, i₂₇: int, volArray₂₈: [int]int, i₂₉: int, volArray₃₀: [int]int, i₃₁: int, i₃₂: int ::
      (  1 < CELLCOUNT₂₁
        && CELLCOUNT₂₁ % 5 == 0
        && CELLCOUNT₂₁ % 5 == 0
        && 1 <= i₂₃
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₂₃
                 ==> 2 <= 8
                    && i₄ <= CELLCOUNT₂₁ / 5
                    && volArray₂₂[-5 + 5 * i₄] == 8
                  ||   (2 <= 8
                       ==> false)
                    && i₄ <= CELLCOUNT₂₁ / 5
                    && volArray₂₂[-5 + 5 * i₄] == 0))
        && (forall i₄: int ::
                  1 <= i₄
                  && i₄ < i₂₃
                || volArray₂₂[-5 + 5 * i₄] == volArray[-5 + 5 * i₄])
        && 1 <= i₂₅
        && (forall i₇: int ::
              (  1 <= i₇
                && i₇ < i₂₅
                 ==> 2 <= 5
                    && i₇ <= CELLCOUNT₂₁ / 5
                    && volArray₂₄[-4 + 5 * i₇] == 5
                  ||   (2 <= 5
                       ==> false)
                    && i₇ <= CELLCOUNT₂₁ / 5
                    && volArray₂₄[-4 + 5 * i₇] == 0))
        && (forall i₇: int ::
                  1 <= i₇
                  && i₇ < i₂₅
                || volArray₂₄[-4 + 5 * i₇] == volArray₂₂[-4 + 5 * i₇])
        && 1 <= i₂₇
        && (forall i₁₀: int ::
              (  1 <= i₁₀
                && i₁₀ < i₂₇
                 ==> 2 <= 7
                    && i₁₀ <= CELLCOUNT₂₁ / 5
                    && volArray₂₆[-3 + 5 * i₁₀] == 7
                  ||   (2 <= 7
                       ==> false)
                    && i₁₀ <= CELLCOUNT₂₁ / 5
                    && volArray₂₆[-3 + 5 * i₁₀] == 0))
        && (forall i₁₀: int ::
                  1 <= i₁₀
                  && i₁₀ < i₂₇
                || volArray₂₆[-3 + 5 * i₁₀] == volArray₂₄[-3 + 5 * i₁₀])
        && 1 <= i₂₉
        && (forall i₁₃: int ::
              (  1 <= i₁₃
                && i₁₃ < i₂₉
                 ==> 2 <= 3
                    && i₁₃ <= CELLCOUNT₂₁ / 5
                    && volArray₂₈[-2 + 5 * i₁₃] == 3
                  ||   (2 <= 3
                       ==> false)
                    && i₁₃ <= CELLCOUNT₂₁ / 5
                    && volArray₂₈[-2 + 5 * i₁₃] == 0))
        && (forall i₁₃: int ::
                  1 <= i₁₃
                  && i₁₃ < i₂₉
                || volArray₂₈[-2 + 5 * i₁₃] == volArray₂₆[-2 + 5 * i₁₃])
        && 1 <= i₃₁
        && (forall i₁₆: int ::
              (  1 <= i₁₆
                && i₁₆ < i₃₁
                 ==> 2 <= 1
                    && i₁₆ <= CELLCOUNT₂₁ / 5
                    && volArray₃₀[-1 + 5 * i₁₆] == 1
                  ||   (2 <= 1
                       ==> false)
                    && i₁₆ <= CELLCOUNT₂₁ / 5
                    && volArray₃₀[-1 + 5 * i₁₆] == 0))
        && (forall i₁₆: int ::
                  1 <= i₁₆
                  && i₁₆ < i₃₁
                || volArray₃₀[-1 + 5 * i₁₆] == volArray₂₈[-1 + 5 * i₁₆])
        && 0 <= i₃₂
        && (forall i₁₉: int ::
              (  0 <= i₁₉
                && i₁₉ < i₃₂
                 ==> i₁₉ < CELLCOUNT₂₁))
        && i₃₂ < CELLCOUNT₂₁
         ==> i₃₁ <= CELLCOUNT₂₁ / 5
          || i₂₉ <= CELLCOUNT₂₁ / 5
          || i₂₇ <= CELLCOUNT₂₁ / 5
          || i₂₅ <= CELLCOUNT₂₁ / 5
          || i₂₃ <= CELLCOUNT₂₁ / 5
          || 2 <= volArray₃₀[i₃₂]
          || volArray₃₀[i₃₂] == 0));


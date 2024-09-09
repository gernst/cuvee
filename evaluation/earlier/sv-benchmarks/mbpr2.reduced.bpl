data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall CELLCOUNT₁₂: int, volArray: [int]int, volArray₁₃: [int]int, i₁₄: int, volArray₁₅: [int]int, i₁₆: int, i₁₇: int ::
      (  1 < CELLCOUNT₁₂
        && CELLCOUNT₁₂ % 2 == 0
        && CELLCOUNT₁₂ % 2 == 0
        && 1 <= i₁₄
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₁₄
                 ==> 2 <= 3
                    && i₄ <= CELLCOUNT₁₂ / 2
                    && volArray₁₃[-2 + 2 * i₄] == 3
                  ||   (2 <= 3
                       ==> false)
                    && i₄ <= CELLCOUNT₁₂ / 2
                    && volArray₁₃[-2 + 2 * i₄] == 0))
        && (forall i₄: int ::
                  1 <= i₄
                  && i₄ < i₁₄
                || volArray₁₃[-2 + 2 * i₄] == volArray[-2 + 2 * i₄])
        && 1 <= i₁₆
        && (forall i₇: int ::
              (  1 <= i₇
                && i₇ < i₁₆
                 ==> 2 <= 1
                    && i₇ <= CELLCOUNT₁₂ / 2
                    && volArray₁₅[-1 + 2 * i₇] == 1
                  ||   (2 <= 1
                       ==> false)
                    && i₇ <= CELLCOUNT₁₂ / 2
                    && volArray₁₅[-1 + 2 * i₇] == 0))
        && (forall i₇: int ::
                  1 <= i₇
                  && i₇ < i₁₆
                || volArray₁₅[-1 + 2 * i₇] == volArray₁₃[-1 + 2 * i₇])
        && 0 <= i₁₇
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₁₇
                 ==> i₁₀ < CELLCOUNT₁₂))
        && i₁₇ < CELLCOUNT₁₂
         ==> i₁₆ <= CELLCOUNT₁₂ / 2
          || i₁₄ <= CELLCOUNT₁₂ / 2
          || 2 <= volArray₁₅[i₁₇]
          || volArray₁₅[i₁₇] == 0));


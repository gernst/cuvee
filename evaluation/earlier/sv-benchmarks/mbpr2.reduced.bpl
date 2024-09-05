data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall CELLCOUNT₁₄: int, volArray: [int]int, volArray₁₅: [int]int, i₁₆: int, volArray₁₇: [int]int, i₁₈: int, x₉: int ::
      (  1 < CELLCOUNT₁₄
        && CELLCOUNT₁₄ % 2 == 0
        && CELLCOUNT₁₄ % 2 == 0
        && 1 <= i₁₆
        && i₁₆ <= 1 + CELLCOUNT₁₄ / 2
        && (forall x₅: int, i₄: int ::
              (  (x₅ == -1 + 2 * i₄
                   ==> 1 <= i₄
                    && i₄ < i₁₆)
                &&   x₅ == -1 + 2 * i₄
                  ||   x₅ == -2 + 2 * i₄
                    && 1 <= i₄
                    && i₄ < i₁₆
                && 2 <= 3
                 ==> (exists i₄: int ::
                        2 <= 3
                        && i₄ <= CELLCOUNT₁₄ / 2
                        && if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < i₁₆ && volArray₁₅[x₅] == volArray₁₅[-2 + 2 * i₄ := 3][-1 + 2 * i₄] else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < i₁₆ && volArray₁₅[x₅] == 3)))
        && (forall x₅: int ::
                (exists i₄: int ::
                      if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < i₁₆ else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < i₁₆)
                || volArray₁₅[x₅] == volArray[x₅])
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₁₆
                 ==> i₄ <= CELLCOUNT₁₄ / 2))
        && 1 <= i₁₈
        && i₁₈ <= 1 + CELLCOUNT₁₄ / 2
        && (forall x₁₇₃: int, i₈: int ::
              (  (x₁₇₃ == -2 + 2 * i₈
                   ==> 1 <= i₈
                    && i₈ < i₁₈)
                &&   x₁₇₃ == -2 + 2 * i₈
                  ||   x₁₇₃ == -1 + 2 * i₈
                    && 1 <= i₈
                    && i₈ < i₁₈
                && 2 <= 1
                 ==> (exists i₈: int ::
                        2 <= 1
                        && i₈ <= CELLCOUNT₁₄ / 2
                        && if(x₁₇₃ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < i₁₈ && volArray₁₇[x₁₇₃] == volArray₁₇[-1 + 2 * i₈ := 1][-2 + 2 * i₈] else x₁₇₃ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < i₁₈ && volArray₁₇[x₁₇₃] == 1)))
        && (forall x₁₇₄: int ::
                (exists i₈: int ::
                      if(x₁₇₄ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < i₁₈ else x₁₇₄ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < i₁₈)
                || volArray₁₇[x₁₇₄] == volArray₁₅[x₁₇₄])
        && (forall i₈: int ::
              (  1 <= i₈
                && i₈ < i₁₈
                 ==> i₈ <= CELLCOUNT₁₄ / 2))
        && i₁₈ <= CELLCOUNT₁₄ / 2
        && (forall i₈: int ::
              (  (x₉ == -2 + 2 * i₈
                   ==> 1 <= i₈
                    && i₈ < i₁₈ + 1)
                &&   x₉ == -2 + 2 * i₈
                  ||   x₉ == -1 + 2 * i₈
                    && 1 <= i₈
                    && i₈ < i₁₈ + 1
                 ==> false))
         ==> 2 <= 1
          || i₁₆ <= CELLCOUNT₁₄ / 2
          || volArray₁₇[i₁₈ * 2 - 1 := 0][i₁₈ * 2 - 2 := volArray₁₇[i₁₈ * 2 - 1 := 0][i₁₈ * 2 - 2]][x₉] == volArray₁₅[x₉]));

goal (forall CELLCOUNT₁₄: int, volArray: [int]int, volArray₁₅: [int]int, i₁₆: int, volArray₁₇: [int]int, i₁₈: int, i₁₉: int ::
      (  1 < CELLCOUNT₁₄
        && CELLCOUNT₁₄ % 2 == 0
        && CELLCOUNT₁₄ % 2 == 0
        && 1 <= i₁₆
        && i₁₆ <= 1 + CELLCOUNT₁₄ / 2
        && (forall x₅: int, i₄: int ::
              (  (x₅ == -1 + 2 * i₄
                   ==> 1 <= i₄
                    && i₄ < i₁₆)
                &&   x₅ == -1 + 2 * i₄
                  ||   x₅ == -2 + 2 * i₄
                    && 1 <= i₄
                    && i₄ < i₁₆
                && 2 <= 3
                 ==> (exists i₄: int ::
                        2 <= 3
                        && i₄ <= CELLCOUNT₁₄ / 2
                        && if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < i₁₆ && volArray₁₅[x₅] == volArray₁₅[-2 + 2 * i₄ := 3][-1 + 2 * i₄] else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < i₁₆ && volArray₁₅[x₅] == 3)))
        && (forall x₅: int ::
                (exists i₄: int ::
                      if(x₅ == -1 + 2 * i₄) then 1 <= i₄ && i₄ < i₁₆ else x₅ == -2 + 2 * i₄ && 1 <= i₄ && i₄ < i₁₆)
                || volArray₁₅[x₅] == volArray[x₅])
        && (forall i₄: int ::
              (  1 <= i₄
                && i₄ < i₁₆
                 ==> i₄ <= CELLCOUNT₁₄ / 2))
        && 1 <= i₁₈
        && i₁₈ <= 1 + CELLCOUNT₁₄ / 2
        && (forall x₉: int, i₈: int ::
              (  (x₉ == -2 + 2 * i₈
                   ==> 1 <= i₈
                    && i₈ < i₁₈)
                &&   x₉ == -2 + 2 * i₈
                  ||   x₉ == -1 + 2 * i₈
                    && 1 <= i₈
                    && i₈ < i₁₈
                && 2 <= 1
                 ==> (exists i₈: int ::
                        2 <= 1
                        && i₈ <= CELLCOUNT₁₄ / 2
                        && if(x₉ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < i₁₈ && volArray₁₇[x₉] == volArray₁₇[-1 + 2 * i₈ := 1][-2 + 2 * i₈] else x₉ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < i₁₈ && volArray₁₇[x₉] == 1)))
        && (forall x₉: int ::
                (exists i₈: int ::
                      if(x₉ == -2 + 2 * i₈) then 1 <= i₈ && i₈ < i₁₈ else x₉ == -1 + 2 * i₈ && 1 <= i₈ && i₈ < i₁₈)
                || volArray₁₇[x₉] == volArray₁₅[x₉])
        && (forall i₈: int ::
              (  1 <= i₈
                && i₈ < i₁₈
                 ==> i₈ <= CELLCOUNT₁₄ / 2))
        && 0 <= i₁₉
        && i₁₉ <= CELLCOUNT₁₄
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₁₉
                 ==> i₁₂ < CELLCOUNT₁₄))
        && i₁₉ < CELLCOUNT₁₄
         ==> i₁₈ <= CELLCOUNT₁₄ / 2
          || i₁₆ <= CELLCOUNT₁₄ / 2
          || 2 <= volArray₁₇[i₁₉]
          || volArray₁₇[i₁₉] == 0));


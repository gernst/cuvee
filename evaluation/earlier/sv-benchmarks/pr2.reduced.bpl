data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall CELLCOUNT₁₁: int, MINVAL: int, volArray: [int]int, volArray₁₂: [int]int, i₁₃: int, x₆: int ::
      (  1 < CELLCOUNT₁₁
        && CELLCOUNT₁₁ % 2 == 0
        && CELLCOUNT₁₁ % 2 == 0
        && 1 <= i₁₃
        && i₁₃ <= 1 + CELLCOUNT₁₁ / 2
        && (forall x₅₉: int, i₅: int ::
              (  (x₅₉ == -1 + 2 * i₅
                   ==> 1 <= i₅
                    && i₅ < i₁₃)
                &&   x₅₉ == -1 + 2 * i₅
                  ||   x₅₉ == -2 + 2 * i₅
                    && 1 <= i₅
                    && i₅ < i₁₃
                && MINVAL <= 1
                && MINVAL <= 1
                 ==> (exists i₅: int ::
                          MINVAL <= 1
                          && MINVAL <= 3
                          && i₅ <= CELLCOUNT₁₁ / 2
                          && if(x₅₉ == -1 + 2 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₅₉] == 1 else x₅₉ == -2 + 2 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₅₉] == 3)
                  ||   MINVAL <= 1
                    && (MINVAL <= 3
                       ==> false)))
        && (forall x₆₀: int ::
                (exists i₅: int ::
                      if(x₆₀ == -1 + 2 * i₅) then 1 <= i₅ && i₅ < i₁₃ else x₆₀ == -2 + 2 * i₅ && 1 <= i₅ && i₅ < i₁₃)
                || volArray₁₂[x₆₀] == volArray[x₆₀])
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₃
                 ==> i₅ <= CELLCOUNT₁₁ / 2))
        && i₁₃ <= CELLCOUNT₁₁ / 2
        && MINVAL <= 3
        && MINVAL <= 1
        && (forall i₅: int ::
              (  (x₆ == -1 + 2 * i₅
                   ==> 1 <= i₅
                    && i₅ < i₁₃ + 1)
                &&   x₆ == -1 + 2 * i₅
                  ||   x₆ == -2 + 2 * i₅
                    && 1 <= i₅
                    && i₅ < i₁₃ + 1
                 ==> false))
         ==> volArray₁₂[i₁₃ * 2 - 2 := 3][i₁₃ * 2 - 1 := 1][x₆] == volArray[x₆]));

goal (forall CELLCOUNT₁₁: int, MINVAL: int, volArray: [int]int, volArray₁₂: [int]int, i₁₃: int, i₁₄: int ::
      (  1 < CELLCOUNT₁₁
        && CELLCOUNT₁₁ % 2 == 0
        && CELLCOUNT₁₁ % 2 == 0
        && 1 <= i₁₃
        && i₁₃ <= 1 + CELLCOUNT₁₁ / 2
        && (forall x₆: int, i₅: int ::
              (  (x₆ == -1 + 2 * i₅
                   ==> 1 <= i₅
                    && i₅ < i₁₃)
                &&   x₆ == -1 + 2 * i₅
                  ||   x₆ == -2 + 2 * i₅
                    && 1 <= i₅
                    && i₅ < i₁₃
                && MINVAL <= 1
                && MINVAL <= 1
                 ==> (exists i₅: int ::
                          MINVAL <= 1
                          && MINVAL <= 3
                          && i₅ <= CELLCOUNT₁₁ / 2
                          && if(x₆ == -1 + 2 * i₅) then 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 1 else x₆ == -2 + 2 * i₅ && 1 <= i₅ && i₅ < i₁₃ && volArray₁₂[x₆] == 3)
                  ||   MINVAL <= 1
                    && (MINVAL <= 3
                       ==> false)))
        && (forall x₆: int ::
                (exists i₅: int ::
                      if(x₆ == -1 + 2 * i₅) then 1 <= i₅ && i₅ < i₁₃ else x₆ == -2 + 2 * i₅ && 1 <= i₅ && i₅ < i₁₃)
                || volArray₁₂[x₆] == volArray[x₆])
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₃
                 ==> i₅ <= CELLCOUNT₁₁ / 2))
        && 0 <= i₁₄
        && i₁₄ <= CELLCOUNT₁₁
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₁₄
                 ==> i₉ < CELLCOUNT₁₁))
        && i₁₄ < CELLCOUNT₁₁
         ==> i₁₃ <= CELLCOUNT₁₁ / 2
          || MINVAL <= volArray₁₂[i₁₄]
          || volArray₁₂[i₁₄] == 0));


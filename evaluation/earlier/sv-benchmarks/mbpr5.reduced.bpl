data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall CELLCOUNT₂₆: int, volArray: [int]int, x₅: int, i₄: int ::
      (  1 < CELLCOUNT₂₆
        && CELLCOUNT₂₆ % 5 == 0
        && CELLCOUNT₂₆ % 5 == 0
        && (x₅ == -1 + 5 * i₄
           ==> 1 <= i₄
            && i₄ < 1)
        && (x₅ == -2 + 5 * i₄
           ==> x₅ == -1 + 5 * i₄
            ||   x₅ == -2 + 5 * i₄
              && 1 <= i₄
              && i₄ < 1)
        && 2 <= 8
         ==> (exists i₆₅: int ::
                2 <= 8
                && i₆₅ <= CELLCOUNT₂₆ / 5
                && if(x₅ == -1 + 5 * i₆₅) then 1 <= i₆₅ && i₆₅ < 1 && volArray[x₅] == volArray[-5 + 5 * i₆₅ := 8][-1 + 5 * i₆₅] else if(x₅ == -2 + 5 * i₆₅) then 1 <= i₆₅ && i₆₅ < 1 && volArray[x₅] == volArray[-5 + 5 * i₆₅ := 8][-2 + 5 * i₆₅] else if(x₅ == -3 + 5 * i₆₅) then 1 <= i₆₅ && i₆₅ < 1 && volArray[x₅] == volArray[-5 + 5 * i₆₅ := 8][-3 + 5 * i₆₅] else if(x₅ == -4 + 5 * i₆₅) then 1 <= i₆₅ && i₆₅ < 1 && volArray[x₅] == volArray[-5 + 5 * i₆₅ := 8][-4 + 5 * i₆₅] else x₅ == -5 + 5 * i₆₅ && 1 <= i₆₅ && i₆₅ < 1 && volArray[x₅] == 8)));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall CELLCOUNT₂₂: int, volArray: [int]int, x₅: int, i₄: int ::
      (  1 < CELLCOUNT₂₂
        && CELLCOUNT₂₂ % 4 == 0
        && CELLCOUNT₂₂ % 4 == 0
        && (x₅ == -1 + 4 * i₄
           ==> 1 <= i₄
            && i₄ < 1)
        && (x₅ == -2 + 4 * i₄
           ==> x₅ == -1 + 4 * i₄
            ||   x₅ == -2 + 4 * i₄
              && 1 <= i₄
              && i₄ < 1)
        && 2 <= 5
         ==> (exists i₅₅: int ::
                2 <= 5
                && i₅₅ <= CELLCOUNT₂₂ / 4
                && if(x₅ == -1 + 4 * i₅₅) then 1 <= i₅₅ && i₅₅ < 1 && volArray[x₅] == volArray[-4 + 4 * i₅₅ := 5][-1 + 4 * i₅₅] else if(x₅ == -2 + 4 * i₅₅) then 1 <= i₅₅ && i₅₅ < 1 && volArray[x₅] == volArray[-4 + 4 * i₅₅ := 5][-2 + 4 * i₅₅] else if(x₅ == -3 + 4 * i₅₅) then 1 <= i₅₅ && i₅₅ < 1 && volArray[x₅] == volArray[-4 + 4 * i₅₅ := 5][-3 + 4 * i₅₅] else x₅ == -4 + 4 * i₅₅ && 1 <= i₅₅ && i₅₅ < 1 && volArray[x₅] == 5)));


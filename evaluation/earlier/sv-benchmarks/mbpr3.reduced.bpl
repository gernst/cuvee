data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall CELLCOUNT₁₈: int, volArray: [int]int, x₅: int, i₄: int ::
      (  1 < CELLCOUNT₁₈
        && CELLCOUNT₁₈ % 3 == 0
        && CELLCOUNT₁₈ % 3 == 0
        && (x₅ == -1 + 3 * i₄
           ==> 1 <= i₄
            && i₄ < 1)
        && (x₅ == -2 + 3 * i₄
           ==> x₅ == -1 + 3 * i₄
            ||   x₅ == -2 + 3 * i₄
              && 1 <= i₄
              && i₄ < 1)
        && 2 <= 7
         ==> (exists i₄₅: int ::
                2 <= 7
                && i₄₅ <= CELLCOUNT₁₈ / 3
                && if(x₅ == -1 + 3 * i₄₅) then 1 <= i₄₅ && i₄₅ < 1 && volArray[x₅] == volArray[-3 + 3 * i₄₅ := 7][-1 + 3 * i₄₅] else if(x₅ == -2 + 3 * i₄₅) then 1 <= i₄₅ && i₄₅ < 1 && volArray[x₅] == volArray[-3 + 3 * i₄₅ := 7][-2 + 3 * i₄₅] else x₅ == -3 + 3 * i₄₅ && 1 <= i₄₅ && i₄₅ < 1 && volArray[x₅] == 7)));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, x₄: int, i₃: int ::
      (  (x₄ == 2 + 3 * i₃
           ==> 0 <= i₃
            && i₃ < 0)
        && (x₄ == 1 + 3 * i₃
           ==> x₄ == 2 + 3 * i₃
            ||   x₄ == 1 + 3 * i₃
              && 0 <= i₃
              && i₃ < 0)
         ==> (exists i₁₈: int ::
                i₁₈ <= 100000
                && if(x₄ == 2 + 3 * i₁₈) then 0 <= i₁₈ && i₁₈ < 0 && a[x₄] == 0 else if(x₄ == 1 + 3 * i₁₈) then 0 <= i₁₈ && i₁₈ < 0 && a[x₄] == 0 else x₄ == 3 * i₁₈ && 0 <= i₁₈ && i₁₈ < 0 && a[x₄] == 0)));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, a₉: [int]int, i₁₀: int, i₁₁: int ::
      (  0 <= i₁₀
        && i₁₀ <= 1 + 100000
        && (forall x₄: int, i₃: int ::
              (  (x₄ == 1 + 2 * i₃
                   ==> 0 <= i₃
                    && i₃ < i₁₀)
                &&   x₄ == 1 + 2 * i₃
                  ||   x₄ == 2 * i₃
                    && 0 <= i₃
                    && i₃ < i₁₀
                 ==> (exists i₃: int ::
                        i₃ <= 100000
                        && if(x₄ == 1 + 2 * i₃) then 0 <= i₃ && i₃ < i₁₀ && a₉[x₄] == 0 else x₄ == 2 * i₃ && 0 <= i₃ && i₃ < i₁₀ && a₉[x₄] == 0)))
        && (forall x₄: int ::
                (exists i₃: int ::
                      if(x₄ == 1 + 2 * i₃) then 0 <= i₃ && i₃ < i₁₀ else x₄ == 2 * i₃ && 0 <= i₃ && i₃ < i₁₀)
                || a₉[x₄] == a[x₄])
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₀
                 ==> i₃ <= 100000))
        && 0 <= i₁₁
        && i₁₁ <= 1 + 2 * 100000
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₁₁
                 ==> i₇ <= 2 * 100000))
        && i₁₁ <= 2 * 100000
         ==> i₁₀ <= 100000
          || 0 <= a₉[i₁₁]));


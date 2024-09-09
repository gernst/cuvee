data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a₉: [int]int, i₁₀: int, i₁₁: int ::
      (  0 <= i₁₀
        && (forall i₃: int ::
              (  0 <= i₃
                && i₃ < i₁₀
                 ==> i₃ <= 100000
                  && (forall x₄: int ::
                            x₄ == 1 + 2 * i₃
                            && 0 <= i₃
                            && i₃ < i₁₀
                            && a₉[x₄] == 0
                          ||   (x₄ == 1 + 2 * i₃
                               ==> false)
                            && (x₄ == 2 * i₃
                               ==> 0 <= i₃
                                && i₃ < i₁₀
                                && a₉[x₄] == 0))))
        && 0 <= i₁₁
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₁₁
                 ==> i₇ <= 2 * 100000))
        && i₁₁ <= 2 * 100000
         ==> i₁₀ <= 100000
          || 0 <= a₉[i₁₁]));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall a: [int]int, a₉: [int]int, i₁₀: int, i₃: int ::
      (  1 <= i₁₀
        && (forall i₃₃: int ::
              (  1 <= i₃₃
                && i₃₃ < i₁₀
                 ==> i₃₃ < 100000
                  && a₉[i₃₃] == 1 + a[0 := 7][-1 + i₃₃]))
        && (forall i₃₄: int ::
                  1 <= i₃₄
                  && i₃₄ < i₁₀
                || a₉[i₃₄] == a[0 := 7][i₃₄])
        && i₁₀ < 100000
        && 1 <= i₃
        && i₃ < i₁₀ + 1
         ==> a₉[i₁₀ := a₉[i₁₀ - 1] + 1][i₃] == 1 + a[0 := 7][-1 + i₃]));

goal {:named "assert"} (forall a: [int]int, a₉: [int]int, i₁₀: int, x₁₁: int ::
      (  1 <= i₁₀
        && (forall i₃: int ::
              (  1 <= i₃
                && i₃ < i₁₀
                 ==> i₃ < 100000
                  && a₉[i₃] == 1 + a[0 := 7][-1 + i₃]))
        && (forall i₃: int ::
                  1 <= i₃
                  && i₃ < i₁₀
                || a₉[i₃] == a[0 := 7][i₃])
        && 1 <= x₁₁
        && (forall x₇: int ::
              (  1 <= x₇
                && x₇ < x₁₁
                 ==> x₇ < 100000))
        && x₁₁ < 100000
         ==> i₁₀ < 100000
          || a₉[x₁₁ - 1] <= a₉[x₁₁]));


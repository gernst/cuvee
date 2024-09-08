data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, a₉: [int]int, i₁₀: int, i₃: int ::
      (  1 <= i₁₀
        && i₁₀ <= 100000
        && (forall i₃₆: int ::
              (  1 <= i₃₆
                && i₃₆ < i₁₀
                 ==> i₃₆ < 100000
                  && a₉[i₃₆] == 1 + a[0 := 7][-1 + i₃₆]))
        && (forall i₃₇: int ::
                  1 <= i₃₇
                  && i₃₇ < i₁₀
                || a₉[i₃₇] == a[0 := 7][i₃₇])
        && i₁₀ < 100000
        && 1 <= i₃
        && i₃ < i₁₀ + 1
         ==> a₉[i₁₀ := a₉[i₁₀ - 1] + 1][i₃] == 1 + a[0 := 7][-1 + i₃]));

goal (forall a: [int]int, a₉: [int]int, i₁₀: int, x₁₁: int ::
      (  1 <= i₁₀
        && i₁₀ <= 100000
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
        && x₁₁ <= 100000
        && (forall x₇: int ::
              (  1 <= x₇
                && x₇ < x₁₁
                 ==> x₇ < 100000))
        && x₁₁ < 100000
         ==> i₁₀ < 100000
          || a₉[x₁₁ - 1] <= a₉[x₁₁]));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall a: [int]int, a₁₀: [int]int, i₁₁: int, x₄: int, i₃: int ::
      (  1 <= i₁₁
        && i₁₁ <= 100000
        && (forall x₃₃: int, i₃₄: int ::
              (  x₃₃ == i₃₄
                && 1 <= i₃₄
                && i₃₄ < i₁₁
                 ==> (exists i₃₅: int ::
                        i₃₅ < 100000
                        && x₃₃ == i₃₅
                        && 1 <= i₃₅
                        && i₃₅ < i₁₁
                        && a₁₀[x₃₃] == 1 + a[0 := 7][-1 + i₃₅])))
        && (forall x₃₆: int ::
                (exists i₃₇: int ::
                        x₃₆ == i₃₇
                        && 1 <= i₃₇
                        && i₃₇ < i₁₁)
                || a₁₀[x₃₆] == a[0 := 7][x₃₆])
        && (forall i₃₈: int ::
              (  1 <= i₃₈
                && i₃₈ < i₁₁
                 ==> i₃₈ < 100000))
        && i₁₁ < 100000
        && x₄ == i₃
        && 1 <= i₃
        && i₃ < i₁₁ + 1
         ==> (exists i₃₉: int ::
                i₃₉ < 100000
                && x₄ == i₃₉
                && 1 <= i₃₉
                && i₃₉ < i₁₁ + 1
                && a₁₀[i₁₁ := a₁₀[i₁₁ - 1] + 1][x₄] == 1 + a[0 := 7][-1 + i₃₉])));

goal (forall a: [int]int, a₁₀: [int]int, i₁₁: int, x₁₂: int ::
      (  1 <= i₁₁
        && i₁₁ <= 100000
        && (forall x₄: int, i₃: int ::
              (  x₄ == i₃
                && 1 <= i₃
                && i₃ < i₁₁
                 ==> (exists i₃: int ::
                        i₃ < 100000
                        && x₄ == i₃
                        && 1 <= i₃
                        && i₃ < i₁₁
                        && a₁₀[x₄] == 1 + a[0 := 7][-1 + i₃])))
        && (forall x₄: int ::
                (exists i₃: int ::
                        x₄ == i₃
                        && 1 <= i₃
                        && i₃ < i₁₁)
                || a₁₀[x₄] == a[0 := 7][x₄])
        && (forall i₃: int ::
              (  1 <= i₃
                && i₃ < i₁₁
                 ==> i₃ < 100000))
        && 1 <= x₁₂
        && x₁₂ <= 100000
        && (forall x₈: int ::
              (  1 <= x₈
                && x₈ < x₁₂
                 ==> x₈ < 100000))
        && x₁₂ < 100000
         ==> i₁₁ < 100000
          || a₁₀[x₁₂ - 1] <= a₁₀[x₁₂]));


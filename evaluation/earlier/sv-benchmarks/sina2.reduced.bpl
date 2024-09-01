data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₉: int, sum: [int]int, a: [int]int, a₂₀: [int]int, i₂₁: int, x₁₀: int ::
      (  N₁₉ <= 2147483647 / 4
        && 0 <= i₂₁
        && i₂₁ <= N₁₉
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₁
                 ==> (exists i₅: int ::
                        i₅ < N₁₉
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₁
                        && a₂₀[x₆] == 1)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₁)
                || a₂₀[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₂₁
                 ==> i₅ < N₁₉))
        && x₁₀ == 0
         ==> i₂₁ < N₁₉
          || N₁₉ <= 0
          || (exists i₉: int ::
                  i₉ < N₁₉
                  && x₁₀ == 0
                  && sum[0 := 0][x₁₀] == a₂₀[i₉] + sum[0 := 0][0])));

goal (forall N₁₉: int, sum: [int]int, a: [int]int, a₂₀: [int]int, i₂₁: int, sum₂₂: [int]int, i₂₃: int, x₁₀: int ::
      (  N₁₉ <= 2147483647 / 4
        && 0 <= i₂₁
        && i₂₁ <= N₁₉
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₁
                 ==> (exists i₅: int ::
                        i₅ < N₁₉
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₁
                        && a₂₀[x₆] == 1)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₁)
                || a₂₀[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₂₁
                 ==> i₅ < N₁₉))
        && 0 <= i₂₃
        && i₂₃ <= N₁₉
        && (forall x₁₁₆: int ::
              (x₁₁₆ == 0
                 ==> (exists i₉: int ::
                        i₉ < N₁₉
                        && x₁₁₆ == 0
                        && sum₂₂[x₁₁₆] == a₂₀[i₉] + sum[0 := 0][0])))
        && (forall x₁₁₇: int ::
                x₁₁₇ == 0
                || sum₂₂[x₁₁₇] == sum[0 := 0][x₁₁₇])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₂₃
                 ==> i₉ < N₁₉))
        && i₂₃ < N₁₉
        && x₁₀ == 0
         ==> i₂₁ < N₁₉
          || N₁₉ <= 0
          || (exists i₉: int ::
                  i₉ < N₁₉
                  && x₁₀ == 0
                  && sum₂₂[0 := sum₂₂[0] + a₂₀[i₂₃]][x₁₀] == a₂₀[i₉] + sum[0 := 0][0])));

goal (forall N₁₉: int, sum: [int]int, a: [int]int, a₂₀: [int]int, i₂₁: int, sum₂₂: [int]int, i₂₃: int, a₂₄: [int]int, i₂₅: int, i₂₆: int ::
      (  N₁₉ <= 2147483647 / 4
        && 0 <= i₂₁
        && i₂₁ <= N₁₉
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₁
                 ==> (exists i₅: int ::
                        i₅ < N₁₉
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₁
                        && a₂₀[x₆] == 1)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₁)
                || a₂₀[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₂₁
                 ==> i₅ < N₁₉))
        && 0 <= i₂₃
        && i₂₃ <= N₁₉
        && (forall x₁₀: int ::
              (x₁₀ == 0
                 ==> (exists i₉: int ::
                        i₉ < N₁₉
                        && x₁₀ == 0
                        && sum₂₂[x₁₀] == a₂₀[i₉] + sum[0 := 0][0])))
        && (forall x₁₀: int ::
                x₁₀ == 0
                || sum₂₂[x₁₀] == sum[0 := 0][x₁₀])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₂₃
                 ==> i₉ < N₁₉))
        && 0 <= i₂₅
        && i₂₅ <= N₁₉
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₅
                 ==> (exists i₁₃: int ::
                        i₁₃ < N₁₉
                        && x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₂₅
                        && a₂₄[x₁₄] == sum₂₂[0] + a₂₀[i₁₃])))
        && (forall x₁₄: int ::
                (exists i₁₃: int ::
                        x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₂₅)
                || a₂₄[x₁₄] == a₂₀[x₁₄])
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₅
                 ==> i₁₃ < N₁₉))
        && 0 <= i₂₆
        && i₂₆ <= N₁₉
        && (forall i₁₇: int ::
              (  i₁₇ <= i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₂₆
                 ==> i₁₇ < N₁₉))
        && i₂₆ < N₁₉
         ==> i₂₅ < N₁₉
          || i₂₃ < N₁₉
          || i₂₁ < N₁₉
          || N₁₉ <= 0
          || a₂₄[i₂₆] == N₁₉ + 1));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₅: int, sum: [int]int, x₆: int ::
      (  N₁₅ <= 2147483647 / 4
        && x₆ == 0
         ==> N₁₅ <= 0
          || (exists i₅: int ::
                  i₅ < N₁₅
                  && x₆ == 0
                  && sum[0 := 0][x₆] == 1 + sum[0 := 0][0])));

goal (forall N₁₅: int, sum: [int]int, sum₁₆: [int]int, i₁₇: int, x₆: int ::
      (  N₁₅ <= 2147483647 / 4
        && 0 <= i₁₇
        && i₁₇ <= N₁₅
        && (forall x₄₉: int ::
              (x₄₉ == 0
                 ==> (exists i₅: int ::
                        i₅ < N₁₅
                        && x₄₉ == 0
                        && sum₁₆[x₄₉] == 1 + sum[0 := 0][0])))
        && (forall x₅₀: int ::
                x₅₀ == 0
                || sum₁₆[x₅₀] == sum[0 := 0][x₅₀])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₁₇
                 ==> i₅ < N₁₅))
        && i₁₇ < N₁₅
        && x₆ == 0
         ==> N₁₅ <= 0
          || (exists i₅: int ::
                  i₅ < N₁₅
                  && x₆ == 0
                  && sum₁₆[0 := sum₁₆[0] + 1][x₆] == 1 + sum[0 := 0][0])));

goal (forall N₁₅: int, sum: [int]int, a: [int]int, sum₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, i₂₀: int ::
      (  N₁₅ <= 2147483647 / 4
        && 0 <= i₁₇
        && i₁₇ <= N₁₅
        && (forall x₆: int ::
              (x₆ == 0
                 ==> (exists i₅: int ::
                        i₅ < N₁₅
                        && x₆ == 0
                        && sum₁₆[x₆] == 1 + sum[0 := 0][0])))
        && (forall x₆: int ::
                x₆ == 0
                || sum₁₆[x₆] == sum[0 := 0][x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₁₇
                 ==> i₅ < N₁₅))
        && 0 <= i₁₉
        && i₁₉ <= N₁₅
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == i₉
                && 0 <= i₉
                && i₉ < i₁₉
                 ==> (exists i₉: int ::
                        i₉ < N₁₅
                        && x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₁₉
                        && a₁₈[x₁₀] == sum₁₆[0])))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₁₉)
                || a₁₈[x₁₀] == a[x₁₀])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₁₉
                 ==> i₉ < N₁₅))
        && 0 <= i₂₀
        && i₂₀ <= N₁₅
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₀
                 ==> i₁₃ < N₁₅))
        && i₂₀ < N₁₅
         ==> i₁₉ < N₁₅
          || i₁₇ < N₁₅
          || N₁₅ <= 0
          || a₁₈[i₂₀] == N₁₅));


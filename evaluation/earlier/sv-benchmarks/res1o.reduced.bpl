data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₈: int, sum: [int]int, a: [int]int, a₁₉: [int]int, i₂₀: int, sum₂₁: [int]int, i₂₂: int, i₉: int ::
      (  N₁₈ <= 2147483647 / 4
        && 0 <= i₂₀
        && i₂₀ <= N₁₈
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₀
                 ==> i₆ < N₁₈
                  && a₁₉[i₆] == 1))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₂₀
                || a₁₉[i₆] == a[i₆])
        && 0 <= i₂₂
        && i₂₂ <= N₁₈
        && (forall i₁₄₅: int ::
              (  0 <= i₁₄₅
                && i₁₄₅ < i₂₂
                 ==> i₁₄₅ < N₁₈
                  && sum₂₁[0] == a₁₉[i₁₄₅] + sum[0 := 0][0]))
        && (forall i₁₄₆: int ::
                  0 <= i₁₄₆
                  && i₁₄₆ < i₂₂
                || sum₂₁[0] == sum[0 := 0][0])
        && i₂₂ < N₁₈
         ==> 0 <= i₉
          || i₂₀ < N₁₈
          || N₁₈ <= 0
          || sum₂₁[0 := sum₂₁[0] + a₁₉[i₂₂]][0] == sum[0 := 0][0]));

goal (forall N₁₈: int, sum: [int]int, a: [int]int, a₁₉: [int]int, i₂₀: int, sum₂₁: [int]int, i₂₂: int, i₉: int ::
      (  N₁₈ <= 2147483647 / 4
        && 0 <= i₂₀
        && i₂₀ <= N₁₈
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₀
                 ==> i₆ < N₁₈
                  && a₁₉[i₆] == 1))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₂₀
                || a₁₉[i₆] == a[i₆])
        && 0 <= i₂₂
        && i₂₂ <= N₁₈
        && (forall i₁₅₅: int ::
              (  0 <= i₁₅₅
                && i₁₅₅ < i₂₂
                 ==> i₁₅₅ < N₁₈
                  && sum₂₁[0] == a₁₉[i₁₅₅] + sum[0 := 0][0]))
        && (forall i₁₅₆: int ::
                  0 <= i₁₅₆
                  && i₁₅₆ < i₂₂
                || sum₂₁[0] == sum[0 := 0][0])
        && i₂₂ < N₁₈
         ==> i₉ < i₂₂ + 1
          || i₂₀ < N₁₈
          || N₁₈ <= 0
          || sum₂₁[0 := sum₂₁[0] + a₁₉[i₂₂]][0] == sum[0 := 0][0]));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₈: int, sum: [int]int, a: [int]int, a₁₉: [int]int, i₂₀: int, sum₂₁: [int]int, i₂₂: int, i₉: int ::
      (  N₁₈ <= 2147483647 / 4
        && 0 <= i₂₀
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
        && (forall i₁₂₉: int ::
              (  0 <= i₁₂₉
                && i₁₂₉ < i₂₂
                 ==> i₁₂₉ < N₁₈
                  && sum₂₁[0] == a₁₉[i₁₂₉] + sum[0 := 0][0]))
        && (forall i₁₃₀: int ::
                  0 <= i₁₃₀
                  && i₁₃₀ < i₂₂
                || sum₂₁[0] == sum[0 := 0][0])
        && i₂₂ < N₁₈
         ==> 0 <= i₉
          || i₂₀ < N₁₈
          || N₁₈ <= 0
          || sum₂₁[0 := sum₂₁[0] + a₁₉[i₂₂]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₁₈: int, sum: [int]int, a: [int]int, a₁₉: [int]int, i₂₀: int, sum₂₁: [int]int, i₂₂: int, i₉: int ::
      (  N₁₈ <= 2147483647 / 4
        && 0 <= i₂₀
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
        && (forall i₁₃₉: int ::
              (  0 <= i₁₃₉
                && i₁₃₉ < i₂₂
                 ==> i₁₃₉ < N₁₈
                  && sum₂₁[0] == a₁₉[i₁₃₉] + sum[0 := 0][0]))
        && (forall i₁₄₀: int ::
                  0 <= i₁₄₀
                  && i₁₄₀ < i₂₂
                || sum₂₁[0] == sum[0 := 0][0])
        && i₂₂ < N₁₈
         ==> i₉ < i₂₂ + 1
          || i₂₀ < N₁₈
          || N₁₈ <= 0
          || sum₂₁[0 := sum₂₁[0] + a₁₉[i₂₂]][0] == sum[0 := 0][0]));


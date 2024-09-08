data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₀: int, sum: [int]int, a: [int]int, a₂₁: [int]int, i₂₂: int, sum₂₃: [int]int, i₂₄: int, i₉: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₂
                 ==> i₆ < N₂₀
                  && a₂₁[i₆] == 1))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₂₂
                || a₂₁[i₆] == a[i₆])
        && 0 <= i₂₄
        && i₂₄ <= N₂₀
        && (forall i₁₄₉: int ::
              (  0 <= i₁₄₉
                && i₁₄₉ < i₂₄
                 ==> i₁₄₉ < N₂₀
                  && sum₂₃[0] == a₂₁[i₁₄₉] + sum[0 := 0][0]))
        && (forall i₁₅₀: int ::
                  0 <= i₁₅₀
                  && i₁₅₀ < i₂₄
                || sum₂₃[0] == sum[0 := 0][0])
        && i₂₄ < N₂₀
         ==> 0 <= i₉
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₃[0 := sum₂₃[0] + a₂₁[i₂₄]][0] == sum[0 := 0][0]));

goal (forall N₂₀: int, sum: [int]int, a: [int]int, a₂₁: [int]int, i₂₂: int, sum₂₃: [int]int, i₂₄: int, i₉: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₂
                 ==> i₆ < N₂₀
                  && a₂₁[i₆] == 1))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₂₂
                || a₂₁[i₆] == a[i₆])
        && 0 <= i₂₄
        && i₂₄ <= N₂₀
        && (forall i₁₅₉: int ::
              (  0 <= i₁₅₉
                && i₁₅₉ < i₂₄
                 ==> i₁₅₉ < N₂₀
                  && sum₂₃[0] == a₂₁[i₁₅₉] + sum[0 := 0][0]))
        && (forall i₁₆₀: int ::
                  0 <= i₁₆₀
                  && i₁₆₀ < i₂₄
                || sum₂₃[0] == sum[0 := 0][0])
        && i₂₄ < N₂₀
         ==> i₉ < i₂₄ + 1
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₃[0 := sum₂₃[0] + a₂₁[i₂₄]][0] == sum[0 := 0][0]));


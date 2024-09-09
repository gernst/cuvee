data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₂₀: int, sum: [int]int, a: [int]int, a₂₁: [int]int, i₂₂: int, sum₂₃: [int]int, i₂₄: int, i₉: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
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
        && (forall i₁₃₃: int ::
              (  0 <= i₁₃₃
                && i₁₃₃ < i₂₄
                 ==> i₁₃₃ < N₂₀
                  && sum₂₃[0] == a₂₁[i₁₃₃] + sum[0 := 0][0]))
        && (forall i₁₃₄: int ::
                  0 <= i₁₃₄
                  && i₁₃₄ < i₂₄
                || sum₂₃[0] == sum[0 := 0][0])
        && i₂₄ < N₂₀
         ==> 0 <= i₉
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₃[0 := sum₂₃[0] + a₂₁[i₂₄]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₂₀: int, sum: [int]int, a: [int]int, a₂₁: [int]int, i₂₂: int, sum₂₃: [int]int, i₂₄: int, i₉: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
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
        && (forall i₁₄₃: int ::
              (  0 <= i₁₄₃
                && i₁₄₃ < i₂₄
                 ==> i₁₄₃ < N₂₀
                  && sum₂₃[0] == a₂₁[i₁₄₃] + sum[0 := 0][0]))
        && (forall i₁₄₄: int ::
                  0 <= i₁₄₄
                  && i₁₄₄ < i₂₄
                || sum₂₃[0] == sum[0 := 0][0])
        && i₂₄ < N₂₀
         ==> i₉ < i₂₄ + 1
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₃[0 := sum₂₃[0] + a₂₁[i₂₄]][0] == sum[0 := 0][0]));


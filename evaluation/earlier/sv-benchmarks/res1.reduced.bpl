data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₈: int, sum: [int]int, a: [int]int, b: [int]int, a₁₉: [int]int, i₂₀: int, b₂₁: [int]int, i₂₂: int, sum₂₃: [int]int, i₂₄: int, i₁₂: int ::
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
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₂
                 ==> i₉ < N₁₈
                  && b₂₁[i₉] == 1))
        && (forall i₉: int ::
                  0 <= i₉
                  && i₉ < i₂₂
                || b₂₁[i₉] == b[i₉])
        && 0 <= i₂₄
        && (forall i₂₂₂: int ::
              (  0 <= i₂₂₂
                && i₂₂₂ < i₂₄
                 ==> i₂₂₂ < N₁₈
                  && sum₂₃[0] == a₁₉[i₂₂₂] + sum[0 := 0][0]))
        && (forall i₂₂₃: int ::
                  0 <= i₂₂₃
                  && i₂₂₃ < i₂₄
                || sum₂₃[0] == sum[0 := 0][0])
        && i₂₄ < N₁₈
         ==> 0 <= i₁₂
          || i₂₂ < N₁₈
          || i₂₀ < N₁₈
          || N₁₈ <= 0
          || sum₂₃[0 := sum₂₃[0] + a₁₉[i₂₄]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₁₈: int, sum: [int]int, a: [int]int, b: [int]int, a₁₉: [int]int, i₂₀: int, b₂₁: [int]int, i₂₂: int, sum₂₃: [int]int, i₂₄: int, i₁₂: int ::
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
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₂
                 ==> i₉ < N₁₈
                  && b₂₁[i₉] == 1))
        && (forall i₉: int ::
                  0 <= i₉
                  && i₉ < i₂₂
                || b₂₁[i₉] == b[i₉])
        && 0 <= i₂₄
        && (forall i₂₃₅: int ::
              (  0 <= i₂₃₅
                && i₂₃₅ < i₂₄
                 ==> i₂₃₅ < N₁₈
                  && sum₂₃[0] == a₁₉[i₂₃₅] + sum[0 := 0][0]))
        && (forall i₂₃₆: int ::
                  0 <= i₂₃₆
                  && i₂₃₆ < i₂₄
                || sum₂₃[0] == sum[0 := 0][0])
        && i₂₄ < N₁₈
         ==> i₁₂ < i₂₄ + 1
          || i₂₂ < N₁₈
          || i₂₀ < N₁₈
          || N₁₈ <= 0
          || sum₂₃[0 := sum₂₃[0] + a₁₉[i₂₄]][0] == sum[0 := 0][0]));


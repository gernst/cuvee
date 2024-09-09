data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₀: int, sum: [int]int, a: [int]int, b: [int]int, a₂₁: [int]int, i₂₂: int, b₂₃: [int]int, i₂₄: int, sum₂₅: [int]int, i₂₆: int, i₁₂: int ::
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
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₄
                 ==> i₉ < N₂₀
                  && b₂₃[i₉] == 1))
        && (forall i₉: int ::
                  0 <= i₉
                  && i₉ < i₂₄
                || b₂₃[i₉] == b[i₉])
        && 0 <= i₂₆
        && (forall i₂₂₆: int ::
              (  0 <= i₂₂₆
                && i₂₂₆ < i₂₆
                 ==> i₂₂₆ < N₂₀
                  && sum₂₅[0] == a₂₁[i₂₂₆] + sum[0 := 0][0]))
        && (forall i₂₂₇: int ::
                  0 <= i₂₂₇
                  && i₂₂₇ < i₂₆
                || sum₂₅[0] == sum[0 := 0][0])
        && i₂₆ < N₂₀
         ==> 0 <= i₁₂
          || i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₅[0 := sum₂₅[0] + a₂₁[i₂₆]][0] == sum[0 := 0][0]));

goal (forall N₂₀: int, sum: [int]int, a: [int]int, b: [int]int, a₂₁: [int]int, i₂₂: int, b₂₃: [int]int, i₂₄: int, sum₂₅: [int]int, i₂₆: int, i₁₂: int ::
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
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₄
                 ==> i₉ < N₂₀
                  && b₂₃[i₉] == 1))
        && (forall i₉: int ::
                  0 <= i₉
                  && i₉ < i₂₄
                || b₂₃[i₉] == b[i₉])
        && 0 <= i₂₆
        && (forall i₂₃₉: int ::
              (  0 <= i₂₃₉
                && i₂₃₉ < i₂₆
                 ==> i₂₃₉ < N₂₀
                  && sum₂₅[0] == a₂₁[i₂₃₉] + sum[0 := 0][0]))
        && (forall i₂₄₀: int ::
                  0 <= i₂₄₀
                  && i₂₄₀ < i₂₆
                || sum₂₅[0] == sum[0 := 0][0])
        && i₂₆ < N₂₀
         ==> i₁₂ < i₂₆ + 1
          || i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₅[0 := sum₂₅[0] + a₂₁[i₂₆]][0] == sum[0 := 0][0]));


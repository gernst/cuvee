data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₀: int, sum: [int]int, a: [int]int, b: [int]int, a₂₁: [int]int, i₂₂: int, b₂₃: [int]int, i₂₄: int, sum₂₅: [int]int, i₂₆: int, i₁₂: int ::
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
        && i₂₆ <= N₂₀
        && (forall i₂₅₉: int ::
              (  0 <= i₂₅₉
                && i₂₅₉ < i₂₆
                 ==> i₂₅₉ < N₂₀
                  && sum₂₅[0] == a₂₁[i₂₅₉] + sum[0 := 0][0]))
        && (forall i₂₆₀: int ::
                  0 <= i₂₆₀
                  && i₂₆₀ < i₂₆
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
        && i₂₆ <= N₂₀
        && (forall i₂₇₂: int ::
              (  0 <= i₂₇₂
                && i₂₇₂ < i₂₆
                 ==> i₂₇₂ < N₂₀
                  && sum₂₅[0] == a₂₁[i₂₇₂] + sum[0 := 0][0]))
        && (forall i₂₇₃: int ::
                  0 <= i₂₇₃
                  && i₂₇₃ < i₂₆
                || sum₂₅[0] == sum[0 := 0][0])
        && i₂₆ < N₂₀
         ==> i₁₂ < i₂₆ + 1
          || i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₅[0 := sum₂₅[0] + a₂₁[i₂₆]][0] == sum[0 := 0][0]));


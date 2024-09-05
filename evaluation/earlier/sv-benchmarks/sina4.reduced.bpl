data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₄: int, sum: [int]int, a: [int]int, a₂₅: [int]int, i₂₆: int, x₁₁: int ::
      (  N₂₄ <= 2147483647 / 4
        && 0 <= i₂₆
        && i₂₆ <= N₂₄
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₆
                 ==> (exists i₆: int ::
                        i₆ < N₂₄
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₆
                        && a₂₅[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₆)
                || a₂₅[x₇] == a[x₇])
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₆
                 ==> i₆ < N₂₄))
        && x₁₁ == 0
         ==> i₂₆ < N₂₄
          || N₂₄ <= 0
          || (exists i₁₀: int ::
                  i₁₀ < N₂₄
                  && x₁₁ == 0
                  && sum[0 := 0][x₁₁] == sum[0 := 0][0] + a₂₅[i₁₀])));

goal (forall N₂₄: int, sum: [int]int, a: [int]int, a₂₅: [int]int, i₂₆: int, sum₂₇: [int]int, i₂₈: int, x₁₁: int ::
      (  N₂₄ <= 2147483647 / 4
        && 0 <= i₂₆
        && i₂₆ <= N₂₄
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₆
                 ==> (exists i₆: int ::
                        i₆ < N₂₄
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₆
                        && a₂₅[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₆)
                || a₂₅[x₇] == a[x₇])
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₆
                 ==> i₆ < N₂₄))
        && 0 <= i₂₈
        && i₂₈ <= N₂₄
        && (forall x₁₂₅: int ::
              (x₁₂₅ == 0
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₄
                        && x₁₂₅ == 0
                        && sum₂₇[x₁₂₅] == sum[0 := 0][0] + a₂₅[i₁₀])))
        && (forall x₁₂₆: int ::
                x₁₂₆ == 0
                || sum₂₇[x₁₂₆] == sum[0 := 0][x₁₂₆])
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₈
                 ==> i₁₀ < N₂₄))
        && i₂₈ < N₂₄
        && x₁₁ == 0
         ==> i₂₆ < N₂₄
          || N₂₄ <= 0
          || (exists i₁₀: int ::
                  i₁₀ < N₂₄
                  && x₁₁ == 0
                  && sum₂₇[0 := sum₂₇[0] + a₂₅[i₂₈]][x₁₁] == sum[0 := 0][0] + a₂₅[i₁₀])));

goal (forall N₂₄: int, sum: [int]int, a: [int]int, b: [int]int, a₂₅: [int]int, i₂₆: int, sum₂₇: [int]int, i₂₈: int, a₂₉: [int]int, i₃₀: int, b₃₁: [int]int, i₃₂: int, i₃₃: int ::
      (  N₂₄ <= 2147483647 / 4
        && 0 <= i₂₆
        && i₂₆ <= N₂₄
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₆
                 ==> (exists i₆: int ::
                        i₆ < N₂₄
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₆
                        && a₂₅[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₆)
                || a₂₅[x₇] == a[x₇])
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₆
                 ==> i₆ < N₂₄))
        && 0 <= i₂₈
        && i₂₈ <= N₂₄
        && (forall x₁₁: int ::
              (x₁₁ == 0
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₄
                        && x₁₁ == 0
                        && sum₂₇[x₁₁] == sum[0 := 0][0] + a₂₅[i₁₀])))
        && (forall x₁₁: int ::
                x₁₁ == 0
                || sum₂₇[x₁₁] == sum[0 := 0][x₁₁])
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₈
                 ==> i₁₀ < N₂₄))
        && 0 <= i₃₀
        && i₃₀ <= N₂₄
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₀
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₄
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₀
                        && a₂₉[x₁₅] == a₂₅[i₁₄] + sum₂₇[0])))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₃₀)
                || a₂₉[x₁₅] == a₂₅[x₁₅])
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₀
                 ==> i₁₄ < N₂₄))
        && 0 <= i₃₂
        && i₃₂ <= N₂₄
        && (forall x₁₉: int, i₁₈: int ::
              (  x₁₉ == i₁₈
                && 0 <= i₁₈
                && i₁₈ < i₃₂
                 ==> (exists i₁₈: int ::
                        i₁₈ < N₂₄
                        && x₁₉ == i₁₈
                        && 0 <= i₁₈
                        && i₁₈ < i₃₂
                        && b₃₁[x₁₉] == 1 + a₂₉[i₁₈])))
        && (forall x₁₉: int ::
                (exists i₁₈: int ::
                        x₁₉ == i₁₈
                        && 0 <= i₁₈
                        && i₁₈ < i₃₂)
                || b₃₁[x₁₉] == b[x₁₉])
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₃₂
                 ==> i₁₈ < N₂₄))
        && 0 <= i₃₃
        && i₃₃ <= N₂₄
        && (forall i₂₂: int ::
              (  0 <= i₂₂
                && i₂₂ < i₃₃
                 ==> i₂₂ < N₂₄))
        && i₃₃ < N₂₄
         ==> i₃₂ < N₂₄
          || i₃₀ < N₂₄
          || i₂₈ < N₂₄
          || i₂₆ < N₂₄
          || N₂₄ <= 0
          || b₃₁[i₃₃] == N₂₄ + 2));


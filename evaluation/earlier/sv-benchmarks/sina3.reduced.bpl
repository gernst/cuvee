data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₄: int, sum: [int]int, a: [int]int, b: [int]int, a₂₅: [int]int, i₂₆: int, b₂₇: [int]int, i₂₈: int, x₁₅: int ::
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
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₈
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₄
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₈
                        && b₂₇[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₈)
                || b₂₇[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₈
                 ==> i₁₀ < N₂₄))
        && x₁₅ == 0
         ==> i₂₈ < N₂₄
          || i₂₆ < N₂₄
          || N₂₄ <= 0
          || (exists i₁₄: int ::
                  i₁₄ < N₂₄
                  && x₁₅ == 0
                  && sum[0 := 0][x₁₅] == a₂₅[i₁₄] + sum[0 := 0][0])));

goal (forall N₂₄: int, sum: [int]int, a: [int]int, b: [int]int, a₂₅: [int]int, i₂₆: int, b₂₇: [int]int, i₂₈: int, sum₂₉: [int]int, i₃₀: int, x₁₅: int ::
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
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₈
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₄
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₈
                        && b₂₇[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₈)
                || b₂₇[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₈
                 ==> i₁₀ < N₂₄))
        && 0 <= i₃₀
        && i₃₀ <= N₂₄
        && (forall x₂₁₄: int ::
              (x₂₁₄ == 0
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₄
                        && x₂₁₄ == 0
                        && sum₂₉[x₂₁₄] == a₂₅[i₁₄] + sum[0 := 0][0])))
        && (forall x₂₁₅: int ::
                x₂₁₅ == 0
                || sum₂₉[x₂₁₅] == sum[0 := 0][x₂₁₅])
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₃₀
                 ==> i₁₄ < N₂₄))
        && i₃₀ < N₂₄
        && x₁₅ == 0
         ==> i₂₈ < N₂₄
          || i₂₆ < N₂₄
          || N₂₄ <= 0
          || (exists i₁₄: int ::
                  i₁₄ < N₂₄
                  && x₁₅ == 0
                  && sum₂₉[0 := sum₂₉[0] + a₂₅[i₃₀]][x₁₅] == a₂₅[i₁₄] + sum[0 := 0][0])));

goal (forall N₂₄: int, sum: [int]int, a: [int]int, b: [int]int, a₂₅: [int]int, i₂₆: int, b₂₇: [int]int, i₂₈: int, sum₂₉: [int]int, i₃₀: int, a₃₁: [int]int, i₃₂: int, i₃₃: int ::
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
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₈
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₄
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₈
                        && b₂₇[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₈)
                || b₂₇[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₈
                 ==> i₁₀ < N₂₄))
        && 0 <= i₃₀
        && i₃₀ <= N₂₄
        && (forall x₁₅: int ::
              (x₁₅ == 0
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₄
                        && x₁₅ == 0
                        && sum₂₉[x₁₅] == a₂₅[i₁₄] + sum[0 := 0][0])))
        && (forall x₁₅: int ::
                x₁₅ == 0
                || sum₂₉[x₁₅] == sum[0 := 0][x₁₅])
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
                        && a₃₁[x₁₉] == b₂₇[i₁₈] + sum₂₉[0])))
        && (forall x₁₉: int ::
                (exists i₁₈: int ::
                        x₁₉ == i₁₈
                        && 0 <= i₁₈
                        && i₁₈ < i₃₂)
                || a₃₁[x₁₉] == a₂₅[x₁₉])
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
          || a₃₁[i₃₃] == N₂₄ + 1));


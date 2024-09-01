data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₂: int, sum: [int]int, a: [int]int, a₂₃: [int]int, i₂₄: int, x₁₁: int ::
      (  N₂₂ <= 2147483647 / 4
        && 0 <= i₂₄
        && i₂₄ <= N₂₂
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₄
                 ==> (exists i₆: int ::
                        i₆ < N₂₂
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₄
                        && a₂₃[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₄)
                || a₂₃[x₇] == a[x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₂₄
                 ==> i₆ < N₂₂))
        && x₁₁ == 0
         ==> i₂₄ < N₂₂
          || N₂₂ <= 0
          || (exists i₁₀: int ::
                  i₁₀ < N₂₂
                  && x₁₁ == 0
                  && sum[0 := 0][x₁₁] == sum[0 := 0][0] + a₂₃[i₁₀])));

goal (forall N₂₂: int, sum: [int]int, a: [int]int, a₂₃: [int]int, i₂₄: int, sum₂₅: [int]int, i₂₆: int, x₁₁: int ::
      (  N₂₂ <= 2147483647 / 4
        && 0 <= i₂₄
        && i₂₄ <= N₂₂
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₄
                 ==> (exists i₆: int ::
                        i₆ < N₂₂
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₄
                        && a₂₃[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₄)
                || a₂₃[x₇] == a[x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₂₄
                 ==> i₆ < N₂₂))
        && 0 <= i₂₆
        && i₂₆ <= N₂₂
        && (forall x₁₂₁: int ::
              (x₁₂₁ == 0
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₂
                        && x₁₂₁ == 0
                        && sum₂₅[x₁₂₁] == sum[0 := 0][0] + a₂₃[i₁₀])))
        && (forall x₁₂₂: int ::
                x₁₂₂ == 0
                || sum₂₅[x₁₂₂] == sum[0 := 0][x₁₂₂])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> i₁₀ < N₂₂))
        && i₂₆ < N₂₂
        && x₁₁ == 0
         ==> i₂₄ < N₂₂
          || N₂₂ <= 0
          || (exists i₁₀: int ::
                  i₁₀ < N₂₂
                  && x₁₁ == 0
                  && sum₂₅[0 := sum₂₅[0] + a₂₃[i₂₆]][x₁₁] == sum[0 := 0][0] + a₂₃[i₁₀])));

goal (forall N₂₂: int, sum: [int]int, a: [int]int, b: [int]int, a₂₃: [int]int, i₂₄: int, sum₂₅: [int]int, i₂₆: int, b₂₇: [int]int, i₂₈: int, x₁₉: int ::
      (  N₂₂ <= 2147483647 / 4
        && 0 <= i₂₄
        && i₂₄ <= N₂₂
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₄
                 ==> (exists i₆: int ::
                        i₆ < N₂₂
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₄
                        && a₂₃[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₄)
                || a₂₃[x₇] == a[x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₂₄
                 ==> i₆ < N₂₂))
        && 0 <= i₂₆
        && i₂₆ <= N₂₂
        && (forall x₁₁: int ::
              (x₁₁ == 0
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₂
                        && x₁₁ == 0
                        && sum₂₅[x₁₁] == sum[0 := 0][0] + a₂₃[i₁₀])))
        && (forall x₁₁: int ::
                x₁₁ == 0
                || sum₂₅[x₁₁] == sum[0 := 0][x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> i₁₀ < N₂₂))
        && 0 <= i₂₈
        && i₂₈ <= N₂₂
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₈
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₂
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₂₈
                        && b₂₇[x₁₅] == 1)))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₂₈)
                || b₂₇[x₁₅] == b[x₁₅])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₈
                 ==> i₁₄ < N₂₂))
        && x₁₉ == 0
         ==> i₂₈ < N₂₂
          || i₂₆ < N₂₂
          || i₂₄ < N₂₂
          || N₂₂ <= 0
          || (exists i₁₈: int ::
                  i₁₈ < N₂₂
                  && x₁₉ == 0
                  && sum₂₅[x₁₉] == b₂₇[i₁₈] + sum₂₅[0])));

goal (forall N₂₂: int, sum: [int]int, a: [int]int, b: [int]int, a₂₃: [int]int, i₂₄: int, sum₂₅: [int]int, i₂₆: int, b₂₇: [int]int, i₂₈: int, sum₂₉: [int]int, i₃₀: int, x₁₉: int ::
      (  N₂₂ <= 2147483647 / 4
        && 0 <= i₂₄
        && i₂₄ <= N₂₂
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₄
                 ==> (exists i₆: int ::
                        i₆ < N₂₂
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₄
                        && a₂₃[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₄)
                || a₂₃[x₇] == a[x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₂₄
                 ==> i₆ < N₂₂))
        && 0 <= i₂₆
        && i₂₆ <= N₂₂
        && (forall x₁₁: int ::
              (x₁₁ == 0
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₂
                        && x₁₁ == 0
                        && sum₂₅[x₁₁] == sum[0 := 0][0] + a₂₃[i₁₀])))
        && (forall x₁₁: int ::
                x₁₁ == 0
                || sum₂₅[x₁₁] == sum[0 := 0][x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> i₁₀ < N₂₂))
        && 0 <= i₂₈
        && i₂₈ <= N₂₂
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₈
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₂
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₂₈
                        && b₂₇[x₁₅] == 1)))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₂₈)
                || b₂₇[x₁₅] == b[x₁₅])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₈
                 ==> i₁₄ < N₂₂))
        && 0 <= i₃₀
        && i₃₀ <= N₂₂
        && (forall x₃₂₄: int ::
              (x₃₂₄ == 0
                 ==> (exists i₁₈: int ::
                        i₁₈ < N₂₂
                        && x₃₂₄ == 0
                        && sum₂₉[x₃₂₄] == b₂₇[i₁₈] + sum₂₅[0])))
        && (forall x₃₂₅: int ::
                x₃₂₅ == 0
                || sum₂₉[x₃₂₅] == sum₂₅[x₃₂₅])
        && (forall i₁₈: int ::
              (  i₁₈ <= i₁₈
                && 0 <= i₁₈
                && i₁₈ < i₃₀
                 ==> i₁₈ < N₂₂))
        && i₃₀ < N₂₂
        && x₁₉ == 0
         ==> i₂₈ < N₂₂
          || i₂₆ < N₂₂
          || i₂₄ < N₂₂
          || N₂₂ <= 0
          || (exists i₁₈: int ::
                  i₁₈ < N₂₂
                  && x₁₉ == 0
                  && sum₂₉[0 := sum₂₉[0] + b₂₇[i₃₀]][x₁₉] == b₂₇[i₁₈] + sum₂₅[0])));

goal (forall N₂₂: int, sum: [int]int, a: [int]int, b: [int]int, a₂₃: [int]int, i₂₄: int, sum₂₅: [int]int, i₂₆: int, b₂₇: [int]int, i₂₈: int, sum₂₉: [int]int, i₃₀: int ::
      (  N₂₂ <= 2147483647 / 4
        && 0 <= i₂₄
        && i₂₄ <= N₂₂
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₄
                 ==> (exists i₆: int ::
                        i₆ < N₂₂
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₄
                        && a₂₃[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₄)
                || a₂₃[x₇] == a[x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₂₄
                 ==> i₆ < N₂₂))
        && 0 <= i₂₆
        && i₂₆ <= N₂₂
        && (forall x₁₁: int ::
              (x₁₁ == 0
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₂
                        && x₁₁ == 0
                        && sum₂₅[x₁₁] == sum[0 := 0][0] + a₂₃[i₁₀])))
        && (forall x₁₁: int ::
                x₁₁ == 0
                || sum₂₅[x₁₁] == sum[0 := 0][x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> i₁₀ < N₂₂))
        && 0 <= i₂₈
        && i₂₈ <= N₂₂
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₈
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₂
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₂₈
                        && b₂₇[x₁₅] == 1)))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₂₈)
                || b₂₇[x₁₅] == b[x₁₅])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₈
                 ==> i₁₄ < N₂₂))
        && 0 <= i₃₀
        && i₃₀ <= N₂₂
        && (forall x₁₉: int ::
              (x₁₉ == 0
                 ==> (exists i₁₈: int ::
                        i₁₈ < N₂₂
                        && x₁₉ == 0
                        && sum₂₉[x₁₉] == b₂₇[i₁₈] + sum₂₅[0])))
        && (forall x₁₉: int ::
                x₁₉ == 0
                || sum₂₉[x₁₉] == sum₂₅[x₁₉])
        && (forall i₁₈: int ::
              (  i₁₈ <= i₁₈
                && 0 <= i₁₈
                && i₁₈ < i₃₀
                 ==> i₁₈ < N₂₂))
         ==> i₃₀ < N₂₂
          || i₂₈ < N₂₂
          || i₂₆ < N₂₂
          || i₂₄ < N₂₂
          || N₂₂ <= 0
          || sum₂₉[0] <= 2 * N₂₂));


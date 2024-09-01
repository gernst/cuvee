data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₂: int, sum: [int]int, a: [int]int, b: [int]int, a₂₃: [int]int, i₂₄: int, b₂₅: [int]int, i₂₆: int, x₁₅: int ::
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
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₂
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₆
                        && b₂₅[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₆)
                || b₂₅[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> i₁₀ < N₂₂))
        && x₁₅ == 0
         ==> i₂₆ < N₂₂
          || i₂₄ < N₂₂
          || N₂₂ <= 0
          || (exists i₁₄: int ::
                  i₁₄ < N₂₂
                  && x₁₅ == 0
                  && sum[0 := 0][x₁₅] == a₂₃[i₁₄] + sum[0 := 0][0])));

goal (forall N₂₂: int, sum: [int]int, a: [int]int, b: [int]int, a₂₃: [int]int, i₂₄: int, b₂₅: [int]int, i₂₆: int, sum₂₇: [int]int, i₂₈: int, x₁₅: int ::
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
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₂
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₆
                        && b₂₅[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₆)
                || b₂₅[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> i₁₀ < N₂₂))
        && 0 <= i₂₈
        && i₂₈ <= N₂₂
        && (forall x₂₁₀: int ::
              (x₂₁₀ == 0
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₂
                        && x₂₁₀ == 0
                        && sum₂₇[x₂₁₀] == a₂₃[i₁₄] + sum[0 := 0][0])))
        && (forall x₂₁₁: int ::
                x₂₁₁ == 0
                || sum₂₇[x₂₁₁] == sum[0 := 0][x₂₁₁])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₈
                 ==> i₁₄ < N₂₂))
        && i₂₈ < N₂₂
        && x₁₅ == 0
         ==> i₂₆ < N₂₂
          || i₂₄ < N₂₂
          || N₂₂ <= 0
          || (exists i₁₄: int ::
                  i₁₄ < N₂₂
                  && x₁₅ == 0
                  && sum₂₇[0 := sum₂₇[0] + a₂₃[i₂₈]][x₁₅] == a₂₃[i₁₄] + sum[0 := 0][0])));

goal (forall N₂₂: int, sum: [int]int, a: [int]int, b: [int]int, a₂₃: [int]int, i₂₄: int, b₂₅: [int]int, i₂₆: int, sum₂₇: [int]int, i₂₈: int, x₁₉: int ::
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
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₂
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₆
                        && b₂₅[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₆)
                || b₂₅[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> i₁₀ < N₂₂))
        && 0 <= i₂₈
        && i₂₈ <= N₂₂
        && (forall x₁₅: int ::
              (x₁₅ == 0
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₂
                        && x₁₅ == 0
                        && sum₂₇[x₁₅] == a₂₃[i₁₄] + sum[0 := 0][0])))
        && (forall x₁₅: int ::
                x₁₅ == 0
                || sum₂₇[x₁₅] == sum[0 := 0][x₁₅])
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
                  && sum₂₇[x₁₉] == b₂₅[i₁₈] + sum₂₇[0])));

goal (forall N₂₂: int, sum: [int]int, a: [int]int, b: [int]int, a₂₃: [int]int, i₂₄: int, b₂₅: [int]int, i₂₆: int, sum₂₇: [int]int, i₂₈: int, sum₂₉: [int]int, i₃₀: int, x₁₉: int ::
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
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₂
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₆
                        && b₂₅[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₆)
                || b₂₅[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> i₁₀ < N₂₂))
        && 0 <= i₂₈
        && i₂₈ <= N₂₂
        && (forall x₁₅: int ::
              (x₁₅ == 0
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₂
                        && x₁₅ == 0
                        && sum₂₇[x₁₅] == a₂₃[i₁₄] + sum[0 := 0][0])))
        && (forall x₁₅: int ::
                x₁₅ == 0
                || sum₂₇[x₁₅] == sum[0 := 0][x₁₅])
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
                        && sum₂₉[x₃₂₄] == b₂₅[i₁₈] + sum₂₇[0])))
        && (forall x₃₂₅: int ::
                x₃₂₅ == 0
                || sum₂₉[x₃₂₅] == sum₂₇[x₃₂₅])
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
                  && sum₂₉[0 := sum₂₉[0] + b₂₅[i₃₀]][x₁₉] == b₂₅[i₁₈] + sum₂₇[0])));

goal (forall N₂₂: int, sum: [int]int, a: [int]int, b: [int]int, a₂₃: [int]int, i₂₄: int, b₂₅: [int]int, i₂₆: int, sum₂₇: [int]int, i₂₈: int, sum₂₉: [int]int, i₃₀: int ::
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
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₂
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₆
                        && b₂₅[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₆)
                || b₂₅[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₆
                 ==> i₁₀ < N₂₂))
        && 0 <= i₂₈
        && i₂₈ <= N₂₂
        && (forall x₁₅: int ::
              (x₁₅ == 0
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₂
                        && x₁₅ == 0
                        && sum₂₇[x₁₅] == a₂₃[i₁₄] + sum[0 := 0][0])))
        && (forall x₁₅: int ::
                x₁₅ == 0
                || sum₂₇[x₁₅] == sum[0 := 0][x₁₅])
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
                        && sum₂₉[x₁₉] == b₂₅[i₁₈] + sum₂₇[0])))
        && (forall x₁₉: int ::
                x₁₉ == 0
                || sum₂₉[x₁₉] == sum₂₇[x₁₉])
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


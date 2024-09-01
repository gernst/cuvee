data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₈: int, sum: [int]int, a: [int]int, b: [int]int, a₂₉: [int]int, i₃₀: int, b₃₁: [int]int, i₃₂: int, x₁₅: int ::
      (  N₂₈ <= 2147483647 / 4
        && 0 <= i₃₀
        && i₃₀ <= N₂₈
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₃₀
                 ==> (exists i₆: int ::
                        i₆ < N₂₈
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₃₀
                        && a₂₉[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₃₀)
                || a₂₉[x₇] == a[x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₃₀
                 ==> i₆ < N₂₈))
        && 0 <= i₃₂
        && i₃₂ <= N₂₈
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₈
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₃₂
                        && b₃₁[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₃₂)
                || b₃₁[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> i₁₀ < N₂₈))
        && x₁₅ == 0
         ==> i₃₂ < N₂₈
          || i₃₀ < N₂₈
          || N₂₈ <= 0
          || (exists i₁₄: int ::
                  i₁₄ < N₂₈
                  && x₁₅ == 0
                  && sum[0 := 0][x₁₅] == a₂₉[i₁₄] + sum[0 := 0][0])));

goal (forall N₂₈: int, sum: [int]int, a: [int]int, b: [int]int, a₂₉: [int]int, i₃₀: int, b₃₁: [int]int, i₃₂: int, sum₃₃: [int]int, i₃₄: int, x₁₅: int ::
      (  N₂₈ <= 2147483647 / 4
        && 0 <= i₃₀
        && i₃₀ <= N₂₈
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₃₀
                 ==> (exists i₆: int ::
                        i₆ < N₂₈
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₃₀
                        && a₂₉[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₃₀)
                || a₂₉[x₇] == a[x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₃₀
                 ==> i₆ < N₂₈))
        && 0 <= i₃₂
        && i₃₂ <= N₂₈
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₈
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₃₂
                        && b₃₁[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₃₂)
                || b₃₁[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> i₁₀ < N₂₈))
        && 0 <= i₃₄
        && i₃₄ <= N₂₈
        && (forall x₂₂₂: int ::
              (x₂₂₂ == 0
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₈
                        && x₂₂₂ == 0
                        && sum₃₃[x₂₂₂] == a₂₉[i₁₄] + sum[0 := 0][0])))
        && (forall x₂₂₃: int ::
                x₂₂₃ == 0
                || sum₃₃[x₂₂₃] == sum[0 := 0][x₂₂₃])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₄
                 ==> i₁₄ < N₂₈))
        && i₃₄ < N₂₈
        && x₁₅ == 0
         ==> i₃₂ < N₂₈
          || i₃₀ < N₂₈
          || N₂₈ <= 0
          || (exists i₁₄: int ::
                  i₁₄ < N₂₈
                  && x₁₅ == 0
                  && sum₃₃[0 := sum₃₃[0] + a₂₉[i₃₄]][x₁₅] == a₂₉[i₁₄] + sum[0 := 0][0])));

goal (forall N₂₈: int, sum: [int]int, a: [int]int, b: [int]int, a₂₉: [int]int, i₃₀: int, b₃₁: [int]int, i₃₂: int, sum₃₃: [int]int, i₃₄: int, x₁₉: int ::
      (  N₂₈ <= 2147483647 / 4
        && 0 <= i₃₀
        && i₃₀ <= N₂₈
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₃₀
                 ==> (exists i₆: int ::
                        i₆ < N₂₈
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₃₀
                        && a₂₉[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₃₀)
                || a₂₉[x₇] == a[x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₃₀
                 ==> i₆ < N₂₈))
        && 0 <= i₃₂
        && i₃₂ <= N₂₈
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₈
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₃₂
                        && b₃₁[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₃₂)
                || b₃₁[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> i₁₀ < N₂₈))
        && 0 <= i₃₄
        && i₃₄ <= N₂₈
        && (forall x₁₅: int ::
              (x₁₅ == 0
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₈
                        && x₁₅ == 0
                        && sum₃₃[x₁₅] == a₂₉[i₁₄] + sum[0 := 0][0])))
        && (forall x₁₅: int ::
                x₁₅ == 0
                || sum₃₃[x₁₅] == sum[0 := 0][x₁₅])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₄
                 ==> i₁₄ < N₂₈))
        && x₁₉ == 0
         ==> i₃₄ < N₂₈
          || i₃₂ < N₂₈
          || i₃₀ < N₂₈
          || N₂₈ <= 0
          || (exists i₁₈: int ::
                  i₁₈ < N₂₈
                  && x₁₉ == 0
                  && sum₃₃[x₁₉] == b₃₁[i₁₈] + sum₃₃[0])));

goal (forall N₂₈: int, sum: [int]int, a: [int]int, b: [int]int, a₂₉: [int]int, i₃₀: int, b₃₁: [int]int, i₃₂: int, sum₃₃: [int]int, i₃₄: int, sum₃₅: [int]int, i₃₆: int, x₁₉: int ::
      (  N₂₈ <= 2147483647 / 4
        && 0 <= i₃₀
        && i₃₀ <= N₂₈
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₃₀
                 ==> (exists i₆: int ::
                        i₆ < N₂₈
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₃₀
                        && a₂₉[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₃₀)
                || a₂₉[x₇] == a[x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₃₀
                 ==> i₆ < N₂₈))
        && 0 <= i₃₂
        && i₃₂ <= N₂₈
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₈
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₃₂
                        && b₃₁[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₃₂)
                || b₃₁[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> i₁₀ < N₂₈))
        && 0 <= i₃₄
        && i₃₄ <= N₂₈
        && (forall x₁₅: int ::
              (x₁₅ == 0
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₈
                        && x₁₅ == 0
                        && sum₃₃[x₁₅] == a₂₉[i₁₄] + sum[0 := 0][0])))
        && (forall x₁₅: int ::
                x₁₅ == 0
                || sum₃₃[x₁₅] == sum[0 := 0][x₁₅])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₄
                 ==> i₁₄ < N₂₈))
        && 0 <= i₃₆
        && i₃₆ <= N₂₈
        && (forall x₃₃₆: int ::
              (x₃₃₆ == 0
                 ==> (exists i₁₈: int ::
                        i₁₈ < N₂₈
                        && x₃₃₆ == 0
                        && sum₃₅[x₃₃₆] == b₃₁[i₁₈] + sum₃₃[0])))
        && (forall x₃₃₇: int ::
                x₃₃₇ == 0
                || sum₃₅[x₃₃₇] == sum₃₃[x₃₃₇])
        && (forall i₁₈: int ::
              (  i₁₈ <= i₁₈
                && 0 <= i₁₈
                && i₁₈ < i₃₆
                 ==> i₁₈ < N₂₈))
        && i₃₆ < N₂₈
        && x₁₉ == 0
         ==> i₃₄ < N₂₈
          || i₃₂ < N₂₈
          || i₃₀ < N₂₈
          || N₂₈ <= 0
          || (exists i₁₈: int ::
                  i₁₈ < N₂₈
                  && x₁₉ == 0
                  && sum₃₅[0 := sum₃₅[0] + b₃₁[i₃₆]][x₁₉] == b₃₁[i₁₈] + sum₃₃[0])));

goal (forall N₂₈: int, sum: [int]int, a: [int]int, b: [int]int, a₂₉: [int]int, i₃₀: int, b₃₁: [int]int, i₃₂: int, sum₃₃: [int]int, i₃₄: int, sum₃₅: [int]int, i₃₆: int, a₃₇: [int]int, i₃₈: int, i₃₉: int ::
      (  N₂₈ <= 2147483647 / 4
        && 0 <= i₃₀
        && i₃₀ <= N₂₈
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 0 <= i₆
                && i₆ < i₃₀
                 ==> (exists i₆: int ::
                        i₆ < N₂₈
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₃₀
                        && a₂₉[x₇] == 1)))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₃₀)
                || a₂₉[x₇] == a[x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 0 <= i₆
                && i₆ < i₃₀
                 ==> i₆ < N₂₈))
        && 0 <= i₃₂
        && i₃₂ <= N₂₈
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₈
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₃₂
                        && b₃₁[x₁₁] == 1)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₃₂)
                || b₃₁[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₂
                 ==> i₁₀ < N₂₈))
        && 0 <= i₃₄
        && i₃₄ <= N₂₈
        && (forall x₁₅: int ::
              (x₁₅ == 0
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₈
                        && x₁₅ == 0
                        && sum₃₃[x₁₅] == a₂₉[i₁₄] + sum[0 := 0][0])))
        && (forall x₁₅: int ::
                x₁₅ == 0
                || sum₃₃[x₁₅] == sum[0 := 0][x₁₅])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₄
                 ==> i₁₄ < N₂₈))
        && 0 <= i₃₆
        && i₃₆ <= N₂₈
        && (forall x₁₉: int ::
              (x₁₉ == 0
                 ==> (exists i₁₈: int ::
                        i₁₈ < N₂₈
                        && x₁₉ == 0
                        && sum₃₅[x₁₉] == b₃₁[i₁₈] + sum₃₃[0])))
        && (forall x₁₉: int ::
                x₁₉ == 0
                || sum₃₅[x₁₉] == sum₃₃[x₁₉])
        && (forall i₁₈: int ::
              (  i₁₈ <= i₁₈
                && 0 <= i₁₈
                && i₁₈ < i₃₆
                 ==> i₁₈ < N₂₈))
        && 0 <= i₃₈
        && i₃₈ <= N₂₈
        && (forall x₂₃: int, i₂₂: int ::
              (  x₂₃ == i₂₂
                && 0 <= i₂₂
                && i₂₂ < i₃₈
                 ==> (exists i₂₂: int ::
                        i₂₂ < N₂₈
                        && x₂₃ == i₂₂
                        && 0 <= i₂₂
                        && i₂₂ < i₃₈
                        && a₃₇[x₂₃] == a₂₉[i₂₂] + sum₃₅[0])))
        && (forall x₂₃: int ::
                (exists i₂₂: int ::
                        x₂₃ == i₂₂
                        && 0 <= i₂₂
                        && i₂₂ < i₃₈)
                || a₃₇[x₂₃] == a₂₉[x₂₃])
        && (forall i₂₂: int ::
              (  i₂₂ <= i₂₂
                && 0 <= i₂₂
                && i₂₂ < i₃₈
                 ==> i₂₂ < N₂₈))
        && 0 <= i₃₉
        && i₃₉ <= N₂₈
        && (forall i₂₆: int ::
              (  i₂₆ <= i₂₆
                && 0 <= i₂₆
                && i₂₆ < i₃₉
                 ==> i₂₆ < N₂₈))
        && i₃₉ < N₂₈
         ==> i₃₈ < N₂₈
          || i₃₆ < N₂₈
          || i₃₄ < N₂₈
          || i₃₂ < N₂₈
          || i₃₀ < N₂₈
          || N₂₈ <= 0
          || a₃₇[i₃₉] == 2 * N₂₈ + 1));


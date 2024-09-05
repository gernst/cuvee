data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₃: int, sum: [int]int, a: [int]int, a₂₄: [int]int, i₂₅: int, x₁₀: int ::
      (  N₂₃ <= 2147483647 / 4
        && 0 <= i₂₅
        && i₂₅ <= N₂₃
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₅
                 ==> (exists i₅: int ::
                        i₅ < N₂₃
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅
                        && a₂₄[x₆] == 1)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅)
                || a₂₄[x₆] == a[x₆])
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₅
                 ==> i₅ < N₂₃))
        && x₁₀ == 0
         ==> i₂₅ < N₂₃
          || N₂₃ <= 0
          || (exists i₉: int ::
                  i₉ < N₂₃
                  && x₁₀ == 0
                  && sum[0 := 0][x₁₀] == a₂₄[i₉] + sum[0 := 0][0])));

goal (forall N₂₃: int, sum: [int]int, a: [int]int, a₂₄: [int]int, i₂₅: int, sum₂₆: [int]int, i₂₇: int, x₁₀: int ::
      (  N₂₃ <= 2147483647 / 4
        && 0 <= i₂₅
        && i₂₅ <= N₂₃
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₅
                 ==> (exists i₅: int ::
                        i₅ < N₂₃
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅
                        && a₂₄[x₆] == 1)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅)
                || a₂₄[x₆] == a[x₆])
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₅
                 ==> i₅ < N₂₃))
        && 0 <= i₂₇
        && i₂₇ <= N₂₃
        && (forall x₁₂₄: int ::
              (x₁₂₄ == 0
                 ==> (exists i₉: int ::
                        i₉ < N₂₃
                        && x₁₂₄ == 0
                        && sum₂₆[x₁₂₄] == a₂₄[i₉] + sum[0 := 0][0])))
        && (forall x₁₂₅: int ::
                x₁₂₅ == 0
                || sum₂₆[x₁₂₅] == sum[0 := 0][x₁₂₅])
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₇
                 ==> i₉ < N₂₃))
        && i₂₇ < N₂₃
        && x₁₀ == 0
         ==> i₂₅ < N₂₃
          || N₂₃ <= 0
          || (exists i₉: int ::
                  i₉ < N₂₃
                  && x₁₀ == 0
                  && sum₂₆[0 := sum₂₆[0] + a₂₄[i₂₇]][x₁₀] == a₂₄[i₉] + sum[0 := 0][0])));

goal (forall N₂₃: int, sum: [int]int, a: [int]int, a₂₄: [int]int, i₂₅: int, sum₂₆: [int]int, i₂₇: int, a₂₈: [int]int, i₂₉: int, a₃₀: [int]int, i₃₁: int, i₃₂: int ::
      (  N₂₃ <= 2147483647 / 4
        && 0 <= i₂₅
        && i₂₅ <= N₂₃
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₅
                 ==> (exists i₅: int ::
                        i₅ < N₂₃
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅
                        && a₂₄[x₆] == 1)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₅)
                || a₂₄[x₆] == a[x₆])
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₅
                 ==> i₅ < N₂₃))
        && 0 <= i₂₇
        && i₂₇ <= N₂₃
        && (forall x₁₀: int ::
              (x₁₀ == 0
                 ==> (exists i₉: int ::
                        i₉ < N₂₃
                        && x₁₀ == 0
                        && sum₂₆[x₁₀] == a₂₄[i₉] + sum[0 := 0][0])))
        && (forall x₁₀: int ::
                x₁₀ == 0
                || sum₂₆[x₁₀] == sum[0 := 0][x₁₀])
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₇
                 ==> i₉ < N₂₃))
        && 0 <= i₂₉
        && i₂₉ <= N₂₃
        && (forall x₁₄: int, i₁₃: int ::
              (  x₁₄ == i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> (exists i₁₃: int ::
                        i₁₃ < N₂₃
                        && x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₂₉
                        && a₂₈[x₁₄] == sum₂₆[0] + a₂₄[i₁₃])))
        && (forall x₁₄: int ::
                (exists i₁₃: int ::
                        x₁₄ == i₁₃
                        && 0 <= i₁₃
                        && i₁₃ < i₂₉)
                || a₂₈[x₁₄] == a₂₄[x₁₄])
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₉
                 ==> i₁₃ < N₂₃))
        && 0 <= i₃₁
        && i₃₁ <= N₂₃
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₃₁
                 ==> (exists i₁₇: int ::
                        i₁₇ < N₂₃
                        && x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₃₁
                        && a₃₀[x₁₈] == a₂₈[i₁₇] % (1 + sum₂₆[0]))))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₃₁)
                || a₃₀[x₁₈] == a₂₈[x₁₈])
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₃₁
                 ==> i₁₇ < N₂₃))
        && 0 <= i₃₂
        && i₃₂ <= N₂₃
        && (forall i₂₁: int ::
              (  0 <= i₂₁
                && i₂₁ < i₃₂
                 ==> i₂₁ < N₂₃))
        && i₃₂ < N₂₃
         ==> i₃₁ < N₂₃
          || i₂₉ < N₂₃
          || i₂₇ < N₂₃
          || i₂₅ < N₂₃
          || N₂₃ <= 0
          || a₃₀[i₃₂] == 0));


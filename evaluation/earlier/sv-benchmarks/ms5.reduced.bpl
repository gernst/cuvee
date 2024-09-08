data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && i₁₃ <= N₁₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 5))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₂₂₇: int ::
              (  0 <= i₂₂₇
                && i₂₂₇ < i₁₅
                 ==> i₂₂₇ == 0
                    && i₂₂₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₂₂₇ == 0
                       ==> false)
                    && i₂₂₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₂₂₇] + sum[0]))
        && (forall i₂₂₈: int ::
                  0 <= i₂₂₈
                  && i₂₂₈ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && i₁₅ == 0
         ==> 0 <= i₈
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := 0][0] == sum[0]));

goal (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && i₁₃ <= N₁₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 5))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₂₃₇: int ::
              (  0 <= i₂₃₇
                && i₂₃₇ < i₁₅
                 ==> i₂₃₇ == 0
                    && i₂₃₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₂₃₇ == 0
                       ==> false)
                    && i₂₃₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₂₃₇] + sum[0]))
        && (forall i₂₃₈: int ::
                  0 <= i₂₃₈
                  && i₂₃₈ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && i₁₅ == 0
         ==> i₈ < i₁₅ + 1
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := 0][0] == sum[0]));

goal (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && i₁₃ <= N₁₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 5))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₃₀₉: int ::
              (  0 <= i₃₀₉
                && i₃₀₉ < i₁₅
                 ==> i₃₀₉ == 0
                    && i₃₀₉ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₀₉ == 0
                       ==> false)
                    && i₃₀₉ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₀₉] + sum[0]))
        && (forall i₃₁₀: int ::
                  0 <= i₃₁₀
                  && i₃₁₀ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && 0 <= i₈
        && i₈ < i₁₅ + 1
        && i₈ == 0
         ==> i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == 0));

goal (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && i₁₃ <= N₁₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 5))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₃₂₇: int ::
              (  0 <= i₃₂₇
                && i₃₂₇ < i₁₅
                 ==> i₃₂₇ == 0
                    && i₃₂₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₂₇ == 0
                       ==> false)
                    && i₃₂₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₂₇] + sum[0]))
        && (forall i₃₂₈: int ::
                  0 <= i₃₂₈
                  && i₃₂₈ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && 0 <= i₈
        && i₈ < i₁₅ + 1
         ==> i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == a₁₂[i₈] + sum[0]));

goal (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && i₁₃ <= N₁₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 5))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₃₃₇: int ::
              (  0 <= i₃₃₇
                && i₃₃₇ < i₁₅
                 ==> i₃₃₇ == 0
                    && i₃₃₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₃₇ == 0
                       ==> false)
                    && i₃₃₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₃₇] + sum[0]))
        && (forall i₃₃₈: int ::
                  0 <= i₃₃₈
                  && i₃₃₈ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> 0 <= i₈
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));

goal (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && i₁₃ <= N₁₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 5))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₃₄₇: int ::
              (  0 <= i₃₄₇
                && i₃₄₇ < i₁₅
                 ==> i₃₄₇ == 0
                    && i₃₄₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₄₇ == 0
                       ==> false)
                    && i₃₄₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₄₇] + sum[0]))
        && (forall i₃₄₈: int ::
                  0 <= i₃₄₈
                  && i₃₄₈ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> i₈ < i₁₅ + 1
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));


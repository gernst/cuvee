data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 1 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 1
                  ||   (i₅ % 1 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₃₂₅: int ::
              (  0 <= i₃₂₅
                && i₃₂₅ < i₁₅
                 ==> i₃₂₅ == 0
                    && i₃₂₅ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₂₅ == 0
                       ==> false)
                    && i₃₂₅ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₂₅] + sum[0]))
        && (forall i₃₂₆: int ::
                  0 <= i₃₂₆
                  && i₃₂₆ < i₁₅
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
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 1 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 1
                  ||   (i₅ % 1 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₃₃₅: int ::
              (  0 <= i₃₃₅
                && i₃₃₅ < i₁₅
                 ==> i₃₃₅ == 0
                    && i₃₃₅ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₃₅ == 0
                       ==> false)
                    && i₃₃₅ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₃₅] + sum[0]))
        && (forall i₃₃₆: int ::
                  0 <= i₃₃₆
                  && i₃₃₆ < i₁₅
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
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 1 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 1
                  ||   (i₅ % 1 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₄₀₀: int ::
              (  0 <= i₄₀₀
                && i₄₀₀ < i₁₅
                 ==> i₄₀₀ == 0
                    && i₄₀₀ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₀₀ == 0
                       ==> false)
                    && i₄₀₀ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₀₀] + sum[0]))
        && (forall i₄₀₁: int ::
                  0 <= i₄₀₁
                  && i₄₀₁ < i₁₅
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
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 1 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 1
                  ||   (i₅ % 1 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₄₂₆: int ::
              (  0 <= i₄₂₆
                && i₄₂₆ < i₁₅
                 ==> i₄₂₆ == 0
                    && i₄₂₆ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₂₆ == 0
                       ==> false)
                    && i₄₂₆ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₂₆] + sum[0]))
        && (forall i₄₂₇: int ::
                  0 <= i₄₂₇
                  && i₄₂₇ < i₁₅
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
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 1 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 1
                  ||   (i₅ % 1 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₄₃₆: int ::
              (  0 <= i₄₃₆
                && i₄₃₆ < i₁₅
                 ==> i₄₃₆ == 0
                    && i₄₃₆ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₃₆ == 0
                       ==> false)
                    && i₄₃₆ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₃₆] + sum[0]))
        && (forall i₄₃₇: int ::
                  0 <= i₄₃₇
                  && i₄₃₇ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> i₈ < i₁₅ + 1
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));


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
        && i₁₅ <= N₁₁
        && (forall i₃₄₅: int ::
              (  0 <= i₃₄₅
                && i₃₄₅ < i₁₅
                 ==> i₃₄₅ == 0
                    && i₃₄₅ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₄₅ == 0
                       ==> false)
                    && i₃₄₅ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₄₅] + sum[0]))
        && (forall i₃₄₆: int ::
                  0 <= i₃₄₆
                  && i₃₄₆ < i₁₅
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
        && i₁₅ <= N₁₁
        && (forall i₃₅₅: int ::
              (  0 <= i₃₅₅
                && i₃₅₅ < i₁₅
                 ==> i₃₅₅ == 0
                    && i₃₅₅ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₅₅ == 0
                       ==> false)
                    && i₃₅₅ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₅₅] + sum[0]))
        && (forall i₃₅₆: int ::
                  0 <= i₃₅₆
                  && i₃₅₆ < i₁₅
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
        && i₁₅ <= N₁₁
        && (forall i₄₂₇: int ::
              (  0 <= i₄₂₇
                && i₄₂₇ < i₁₅
                 ==> i₄₂₇ == 0
                    && i₄₂₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₂₇ == 0
                       ==> false)
                    && i₄₂₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₂₇] + sum[0]))
        && (forall i₄₂₈: int ::
                  0 <= i₄₂₈
                  && i₄₂₈ < i₁₅
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
        && i₁₅ <= N₁₁
        && (forall i₄₅₃: int ::
              (  0 <= i₄₅₃
                && i₄₅₃ < i₁₅
                 ==> i₄₅₃ == 0
                    && i₄₅₃ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₅₃ == 0
                       ==> false)
                    && i₄₅₃ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₅₃] + sum[0]))
        && (forall i₄₅₄: int ::
                  0 <= i₄₅₄
                  && i₄₅₄ < i₁₅
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
        && i₁₅ <= N₁₁
        && (forall i₄₆₃: int ::
              (  0 <= i₄₆₃
                && i₄₆₃ < i₁₅
                 ==> i₄₆₃ == 0
                    && i₄₆₃ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₆₃ == 0
                       ==> false)
                    && i₄₆₃ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₆₃] + sum[0]))
        && (forall i₄₆₄: int ::
                  0 <= i₄₆₄
                  && i₄₆₄ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> i₈ < i₁₅ + 1
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));


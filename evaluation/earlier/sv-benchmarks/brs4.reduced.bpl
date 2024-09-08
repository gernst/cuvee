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
                 ==> i₅ % 4 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 4
                  ||   (i₅ % 4 == 0
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
                 ==> i₅ % 4 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 4
                  ||   (i₅ % 4 == 0
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
                 ==> i₅ % 4 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 4
                  ||   (i₅ % 4 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₃₉₅: int ::
              (  0 <= i₃₉₅
                && i₃₉₅ < i₁₅
                 ==> i₃₉₅ == 0
                    && i₃₉₅ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₉₅ == 0
                       ==> false)
                    && i₃₉₅ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₉₅] + sum[0]))
        && (forall i₃₉₆: int ::
                  0 <= i₃₉₆
                  && i₃₉₆ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && 0 <= i₈
        && i₈ < i₁₅ + 1
         ==> i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || i₈ == 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == a₁₂[i₈] + sum[0]));

goal (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && i₁₃ <= N₁₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 4 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 4
                  ||   (i₅ % 4 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₄₂₉: int ::
              (  0 <= i₄₂₉
                && i₄₂₉ < i₁₅
                 ==> i₄₂₉ == 0
                    && i₄₂₉ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₂₉ == 0
                       ==> false)
                    && i₄₂₉ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₂₉] + sum[0]))
        && (forall i₄₃₀: int ::
                  0 <= i₄₃₀
                  && i₄₃₀ < i₁₅
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
                 ==> i₅ % 4 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 4
                  ||   (i₅ % 4 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₄₄₇: int ::
              (  0 <= i₄₄₇
                && i₄₄₇ < i₁₅
                 ==> i₄₄₇ == 0
                    && i₄₄₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₄₇ == 0
                       ==> false)
                    && i₄₄₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₄₇] + sum[0]))
        && (forall i₄₄₈: int ::
                  0 <= i₄₄₈
                  && i₄₄₈ < i₁₅
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
                 ==> i₅ % 4 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 4
                  ||   (i₅ % 4 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₄₅₇: int ::
              (  0 <= i₄₅₇
                && i₄₅₇ < i₁₅
                 ==> i₄₅₇ == 0
                    && i₄₅₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₅₇ == 0
                       ==> false)
                    && i₄₅₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₅₇] + sum[0]))
        && (forall i₄₅₈: int ::
                  0 <= i₄₅₈
                  && i₄₅₈ < i₁₅
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
                 ==> i₅ % 4 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 4
                  ||   (i₅ % 4 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₄₆₇: int ::
              (  0 <= i₄₆₇
                && i₄₆₇ < i₁₅
                 ==> i₄₆₇ == 0
                    && i₄₆₇ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₆₇ == 0
                       ==> false)
                    && i₄₆₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₆₇] + sum[0]))
        && (forall i₄₆₈: int ::
                  0 <= i₄₆₈
                  && i₄₆₈ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> i₈ < i₁₅ + 1
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));


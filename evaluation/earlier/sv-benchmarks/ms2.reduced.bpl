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
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 2))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₂₁₁: int ::
              (  0 <= i₂₁₁
                && i₂₁₁ < i₁₅
                 ==> i₂₁₁ == 0
                    && i₂₁₁ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₂₁₁ == 0
                       ==> false)
                    && i₂₁₁ < N₁₁
                    && sum₁₄[0] == a₁₂[i₂₁₁] + sum[0]))
        && (forall i₂₁₂: int ::
                  0 <= i₂₁₂
                  && i₂₁₂ < i₁₅
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
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 2))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₂₂₁: int ::
              (  0 <= i₂₂₁
                && i₂₂₁ < i₁₅
                 ==> i₂₂₁ == 0
                    && i₂₂₁ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₂₂₁ == 0
                       ==> false)
                    && i₂₂₁ < N₁₁
                    && sum₁₄[0] == a₁₂[i₂₂₁] + sum[0]))
        && (forall i₂₂₂: int ::
                  0 <= i₂₂₂
                  && i₂₂₂ < i₁₅
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
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 2))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₂₈₆: int ::
              (  0 <= i₂₈₆
                && i₂₈₆ < i₁₅
                 ==> i₂₈₆ == 0
                    && i₂₈₆ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₂₈₆ == 0
                       ==> false)
                    && i₂₈₆ < N₁₁
                    && sum₁₄[0] == a₁₂[i₂₈₆] + sum[0]))
        && (forall i₂₈₇: int ::
                  0 <= i₂₈₇
                  && i₂₈₇ < i₁₅
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
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 2))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₃₀₄: int ::
              (  0 <= i₃₀₄
                && i₃₀₄ < i₁₅
                 ==> i₃₀₄ == 0
                    && i₃₀₄ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₀₄ == 0
                       ==> false)
                    && i₃₀₄ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₀₄] + sum[0]))
        && (forall i₃₀₅: int ::
                  0 <= i₃₀₅
                  && i₃₀₅ < i₁₅
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
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 2))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₃₁₄: int ::
              (  0 <= i₃₁₄
                && i₃₁₄ < i₁₅
                 ==> i₃₁₄ == 0
                    && i₃₁₄ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₁₄ == 0
                       ==> false)
                    && i₃₁₄ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₁₄] + sum[0]))
        && (forall i₃₁₅: int ::
                  0 <= i₃₁₅
                  && i₃₁₅ < i₁₅
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
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 2))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₃₂₄: int ::
              (  0 <= i₃₂₄
                && i₃₂₄ < i₁₅
                 ==> i₃₂₄ == 0
                    && i₃₂₄ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₂₄ == 0
                       ==> false)
                    && i₃₂₄ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₂₄] + sum[0]))
        && (forall i₃₂₅: int ::
                  0 <= i₃₂₅
                  && i₃₂₅ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> i₈ < i₁₅ + 1
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));


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
                 ==> i₅ % 2 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 2
                  ||   (i₅ % 2 == 0
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
                 ==> i₅ % 2 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 2
                  ||   (i₅ % 2 == 0
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
                 ==> i₅ % 2 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 2
                  ||   (i₅ % 2 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₃₆₈: int ::
              (  0 <= i₃₆₈
                && i₃₆₈ < i₁₅
                 ==> i₃₆₈ == 0
                    && i₃₆₈ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₃₆₈ == 0
                       ==> false)
                    && i₃₆₈ < N₁₁
                    && sum₁₄[0] == a₁₂[i₃₆₈] + sum[0]))
        && (forall i₃₆₉: int ::
                  0 <= i₃₆₉
                  && i₃₆₉ < i₁₅
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
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ % 2 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 2
                  ||   (i₅ % 2 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₄₀₂: int ::
              (  0 <= i₄₀₂
                && i₄₀₂ < i₁₅
                 ==> i₄₀₂ == 0
                    && i₄₀₂ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₀₂ == 0
                       ==> false)
                    && i₄₀₂ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₀₂] + sum[0]))
        && (forall i₄₀₃: int ::
                  0 <= i₄₀₃
                  && i₄₀₃ < i₁₅
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
                 ==> i₅ % 2 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 2
                  ||   (i₅ % 2 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₄₂₀: int ::
              (  0 <= i₄₂₀
                && i₄₂₀ < i₁₅
                 ==> i₄₂₀ == 0
                    && i₄₂₀ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₂₀ == 0
                       ==> false)
                    && i₄₂₀ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₂₀] + sum[0]))
        && (forall i₄₂₁: int ::
                  0 <= i₄₂₁
                  && i₄₂₁ < i₁₅
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
                 ==> i₅ % 2 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 2
                  ||   (i₅ % 2 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₄₃₀: int ::
              (  0 <= i₄₃₀
                && i₄₃₀ < i₁₅
                 ==> i₄₃₀ == 0
                    && i₄₃₀ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₃₀ == 0
                       ==> false)
                    && i₄₃₀ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₃₀] + sum[0]))
        && (forall i₄₃₁: int ::
                  0 <= i₄₃₁
                  && i₄₃₁ < i₁₅
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
                 ==> i₅ % 2 == 0
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 2
                  ||   (i₅ % 2 == 0
                       ==> false)
                    && i₅ < N₁₁
                    && a₁₂[i₅] == 0))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₄₄₀: int ::
              (  0 <= i₄₄₀
                && i₄₄₀ < i₁₅
                 ==> i₄₄₀ == 0
                    && i₄₄₀ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₄₄₀ == 0
                       ==> false)
                    && i₄₄₀ < N₁₁
                    && sum₁₄[0] == a₁₂[i₄₄₀] + sum[0]))
        && (forall i₄₄₁: int ::
                  0 <= i₄₄₁
                  && i₄₄₁ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> i₈ < i₁₅ + 1
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));


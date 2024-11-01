data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 4))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₀₃: int ::
              (  0 <= i₁₀₃
                && i₁₀₃ < i₁₅
                 ==> i₁₀₃ == 0
                    && i₁₀₃ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₁₀₃ == 0
                       ==> false)
                    && i₁₀₃ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₀₃] + sum[0]))
        && (forall i₁₀₄: int ::
                  0 <= i₁₀₄
                  && i₁₀₄ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && i₁₅ == 0
         ==> 0 <= i₈
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := 0][0] == sum[0]));

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 4))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₁₃: int ::
              (  0 <= i₁₁₃
                && i₁₁₃ < i₁₅
                 ==> i₁₁₃ == 0
                    && i₁₁₃ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₁₁₃ == 0
                       ==> false)
                    && i₁₁₃ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₁₃] + sum[0]))
        && (forall i₁₁₄: int ::
                  0 <= i₁₁₄
                  && i₁₁₄ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && i₁₅ == 0
         ==> i₈ < i₁₅ + 1
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := 0][0] == sum[0]));

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 4))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₃₀: int ::
              (  0 <= i₁₃₀
                && i₁₃₀ < i₁₅
                 ==> i₁₃₀ == 0
                    && i₁₃₀ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₁₃₀ == 0
                       ==> false)
                    && i₁₃₀ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₃₀] + sum[0]))
        && (forall i₁₃₁: int ::
                  0 <= i₁₃₁
                  && i₁₃₁ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
        && 0 <= i₈
        && i₈ < i₁₅ + 1
         ==> i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          ||   i₈ == 0
            && i₈ < N₁₁
            && sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == 0
          ||   (i₈ == 0
               ==> false)
            && i₈ < N₁₁
            && sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == a₁₂[i₈] + sum[0]));

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 4))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₄₀: int ::
              (  0 <= i₁₄₀
                && i₁₄₀ < i₁₅
                 ==> i₁₄₀ == 0
                    && i₁₄₀ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₁₄₀ == 0
                       ==> false)
                    && i₁₄₀ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₄₀] + sum[0]))
        && (forall i₁₄₁: int ::
                  0 <= i₁₄₁
                  && i₁₄₁ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> 0 <= i₈
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == i₅ % 4))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₅₀: int ::
              (  0 <= i₁₅₀
                && i₁₅₀ < i₁₅
                 ==> i₁₅₀ == 0
                    && i₁₅₀ < N₁₁
                    && sum₁₄[0] == 0
                  ||   (i₁₅₀ == 0
                       ==> false)
                    && i₁₅₀ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₅₀] + sum[0]))
        && (forall i₁₅₁: int ::
                  0 <= i₁₅₁
                  && i₁₅₁ < i₁₅
                || sum₁₄[0] == sum[0])
        && i₁₅ < N₁₁
         ==> i₈ < i₁₅ + 1
          || i₁₅ == 0
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0]));


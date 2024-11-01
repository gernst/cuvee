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
                  && a₁₂[i₅] == 5))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₀₃: int ::
              (  0 <= i₁₀₃
                && i₁₀₃ < i₁₅
                 ==> a₁₂[i₁₀₃] == 5
                    && i₁₀₃ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₀₃] + sum[0 := 0][0]
                  ||   (a₁₂[i₁₀₃] == 5
                       ==> false)
                    && i₁₀₃ < N₁₁
                    && sum₁₄[0] == sum[0 := 0][0] * a₁₂[i₁₀₃]))
        && (forall i₁₀₄: int ::
                  0 <= i₁₀₄
                  && i₁₀₄ < i₁₅
                || sum₁₄[0] == sum[0 := 0][0])
        && i₁₅ < N₁₁
        && a₁₂[i₁₅] == 5
         ==> 0 <= i₈
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == 5))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₁₁₃: int ::
              (  0 <= i₁₁₃
                && i₁₁₃ < i₁₅
                 ==> a₁₂[i₁₁₃] == 5
                    && i₁₁₃ < N₁₁
                    && sum₁₄[0] == a₁₂[i₁₁₃] + sum[0 := 0][0]
                  ||   (a₁₂[i₁₁₃] == 5
                       ==> false)
                    && i₁₁₃ < N₁₁
                    && sum₁₄[0] == sum[0 := 0][0] * a₁₂[i₁₁₃]))
        && (forall i₁₁₄: int ::
                  0 <= i₁₁₄
                  && i₁₁₄ < i₁₅
                || sum₁₄[0] == sum[0 := 0][0])
        && i₁₅ < N₁₁
        && a₁₂[i₁₅] == 5
         ==> i₈ < i₁₅ + 1
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0 := 0][0]));


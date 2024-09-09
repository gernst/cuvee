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
                  && a₁₂[i₅] == 5))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && (forall i₂₁₁: int ::
              (  0 <= i₂₁₁
                && i₂₁₁ < i₁₅
                 ==> a₁₂[i₂₁₁] == 5
                    && i₂₁₁ < N₁₁
                    && sum₁₄[0] == a₁₂[i₂₁₁] + sum[0 := 0][0]
                  ||   (a₁₂[i₂₁₁] == 5
                       ==> false)
                    && i₂₁₁ < N₁₁
                    && sum₁₄[0] == sum[0 := 0][0] * a₁₂[i₂₁₁]))
        && (forall i₂₁₂: int ::
                  0 <= i₂₁₂
                  && i₂₁₂ < i₁₅
                || sum₁₄[0] == sum[0 := 0][0])
        && i₁₅ < N₁₁
        && a₁₂[i₁₅] == 5
         ==> 0 <= i₈
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0 := 0][0]));

goal (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
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
        && (forall i₂₂₁: int ::
              (  0 <= i₂₂₁
                && i₂₂₁ < i₁₅
                 ==> a₁₂[i₂₂₁] == 5
                    && i₂₂₁ < N₁₁
                    && sum₁₄[0] == a₁₂[i₂₂₁] + sum[0 := 0][0]
                  ||   (a₁₂[i₂₂₁] == 5
                       ==> false)
                    && i₂₂₁ < N₁₁
                    && sum₁₄[0] == sum[0 := 0][0] * a₁₂[i₂₂₁]))
        && (forall i₂₂₂: int ::
                  0 <= i₂₂₂
                  && i₂₂₂ < i₁₅
                || sum₁₄[0] == sum[0 := 0][0])
        && i₁₅ < N₁₁
        && a₁₂[i₁₅] == 5
         ==> i₈ < i₁₅ + 1
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0 := 0][0]));


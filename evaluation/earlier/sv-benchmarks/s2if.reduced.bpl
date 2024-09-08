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
                  && a₁₂[i₅] == 2))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₂₂₇: int ::
              (  0 <= i₂₂₇
                && i₂₂₇ < i₁₅
                 ==> a₁₂[i₂₂₇] == 2
                    && i₂₂₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₂₂₇] + sum[0 := 0][0]
                  ||   (a₁₂[i₂₂₇] == 2
                       ==> false)
                    && i₂₂₇ < N₁₁
                    && sum₁₄[0] == sum[0 := 0][0] * a₁₂[i₂₂₇]))
        && (forall i₂₂₈: int ::
                  0 <= i₂₂₈
                  && i₂₂₈ < i₁₅
                || sum₁₄[0] == sum[0 := 0][0])
        && i₁₅ < N₁₁
        && a₁₂[i₁₅] == 2
         ==> 0 <= i₈
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0 := 0][0]));

goal (forall N₁₁: int, sum: [int]int, a: [int]int, a₁₂: [int]int, i₁₃: int, sum₁₄: [int]int, i₁₅: int, i₈: int ::
      (  N₁₁ <= 2147483647 / 4
        && 0 <= i₁₃
        && i₁₃ <= N₁₁
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₃
                 ==> i₅ < N₁₁
                  && a₁₂[i₅] == 2))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₃
                || a₁₂[i₅] == a[i₅])
        && 0 <= i₁₅
        && i₁₅ <= N₁₁
        && (forall i₂₃₇: int ::
              (  0 <= i₂₃₇
                && i₂₃₇ < i₁₅
                 ==> a₁₂[i₂₃₇] == 2
                    && i₂₃₇ < N₁₁
                    && sum₁₄[0] == a₁₂[i₂₃₇] + sum[0 := 0][0]
                  ||   (a₁₂[i₂₃₇] == 2
                       ==> false)
                    && i₂₃₇ < N₁₁
                    && sum₁₄[0] == sum[0 := 0][0] * a₁₂[i₂₃₇]))
        && (forall i₂₃₈: int ::
                  0 <= i₂₃₈
                  && i₂₃₈ < i₁₅
                || sum₁₄[0] == sum[0 := 0][0])
        && i₁₅ < N₁₁
        && a₁₂[i₁₅] == 2
         ==> i₈ < i₁₅ + 1
          || i₁₃ < N₁₁
          || N₁₁ <= 0
          || sum₁₄[0 := sum₁₄[0] + a₁₂[i₁₅]][0] == sum[0 := 0][0]));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₃: int, sum: [int]int, sum₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && i₁₅ <= N₁₃
        && (forall i₆₀: int ::
              (  0 <= i₆₀
                && i₆₀ < i₁₅
                 ==> i₆₀ < N₁₃
                  && sum₁₄[0] == 1 + sum[0 := 0][0]))
        && (forall i₆₁: int ::
                  0 <= i₆₁
                  && i₆₁ < i₁₅
                || sum₁₄[0] == sum[0 := 0][0])
        && i₁₅ < N₁₃
         ==> 0 <= i₅
          || N₁₃ <= 0
          || sum₁₄[0 := sum₁₄[0] + 1][0] == sum[0 := 0][0]));

goal (forall N₁₃: int, sum: [int]int, sum₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && i₁₅ <= N₁₃
        && (forall i₆₇: int ::
              (  0 <= i₆₇
                && i₆₇ < i₁₅
                 ==> i₆₇ < N₁₃
                  && sum₁₄[0] == 1 + sum[0 := 0][0]))
        && (forall i₆₈: int ::
                  0 <= i₆₈
                  && i₆₈ < i₁₅
                || sum₁₄[0] == sum[0 := 0][0])
        && i₁₅ < N₁₃
         ==> i₅ < i₁₅ + 1
          || N₁₃ <= 0
          || sum₁₄[0 := sum₁₄[0] + 1][0] == sum[0 := 0][0]));


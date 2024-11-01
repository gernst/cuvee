data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₃: int, sum: [int]int, sum₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₅₅: int ::
              (  0 <= i₅₅
                && i₅₅ < i₁₅
                 ==> i₅₅ < N₁₃
                  && sum₁₄[0] == 1 + sum[0 := 0][0]))
        && (forall i₅₆: int ::
                  0 <= i₅₆
                  && i₅₆ < i₁₅
                || sum₁₄[0] == sum[0 := 0][0])
        && i₁₅ < N₁₃
         ==> 0 <= i₅
          || N₁₃ <= 0
          || sum₁₄[0 := sum₁₄[0] + 1][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₁₃: int, sum: [int]int, sum₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 0 <= i₁₅
        && (forall i₆₂: int ::
              (  0 <= i₆₂
                && i₆₂ < i₁₅
                 ==> i₆₂ < N₁₃
                  && sum₁₄[0] == 1 + sum[0 := 0][0]))
        && (forall i₆₃: int ::
                  0 <= i₆₃
                  && i₆₃ < i₁₅
                || sum₁₄[0] == sum[0 := 0][0])
        && i₁₅ < N₁₃
         ==> i₅ < i₁₅ + 1
          || N₁₃ <= 0
          || sum₁₄[0 := sum₁₄[0] + 1][0] == sum[0 := 0][0]));


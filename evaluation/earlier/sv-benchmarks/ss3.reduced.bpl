data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₂₀: int, sum: [int]int, a: [int]int, a₂₁: [int]int, i₂₂: int, sum₂₃: [int]int, i₂₄: int, i₈: int ::
      (  -2147483648 <= N₂₀
        && N₂₀ < 2147483648
        && N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> i₅ < N₂₀
                  && a₂₁[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || a₂₁[i₅] == a[i₅])
        && 0 <= i₂₄
        && (forall i₁₃₅: int ::
              (  0 <= i₁₃₅
                && i₁₃₅ < i₂₄
                 ==> i₁₃₅ < N₂₀
                  && sum₂₃[0] == a₂₁[i₁₃₅] + sum[0 := 0][0]))
        && (forall i₁₃₆: int ::
                  0 <= i₁₃₆
                  && i₁₃₆ < i₂₄
                || sum₂₃[0] == sum[0 := 0][0])
        && i₂₄ < N₂₀
         ==> 0 <= i₈
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₃[0 := sum₂₃[0] + a₂₁[i₂₄]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₂₀: int, sum: [int]int, a: [int]int, a₂₁: [int]int, i₂₂: int, sum₂₃: [int]int, i₂₄: int, i₈: int ::
      (  -2147483648 <= N₂₀
        && N₂₀ < 2147483648
        && N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> i₅ < N₂₀
                  && a₂₁[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || a₂₁[i₅] == a[i₅])
        && 0 <= i₂₄
        && (forall i₁₄₅: int ::
              (  0 <= i₁₄₅
                && i₁₄₅ < i₂₄
                 ==> i₁₄₅ < N₂₀
                  && sum₂₃[0] == a₂₁[i₁₄₅] + sum[0 := 0][0]))
        && (forall i₁₄₆: int ::
                  0 <= i₁₄₆
                  && i₁₄₆ < i₂₄
                || sum₂₃[0] == sum[0 := 0][0])
        && i₂₄ < N₂₀
         ==> i₈ < i₂₄ + 1
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₃[0 := sum₂₃[0] + a₂₁[i₂₄]][0] == sum[0 := 0][0]));


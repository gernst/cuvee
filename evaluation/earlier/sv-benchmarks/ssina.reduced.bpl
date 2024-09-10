data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₂₂: int, sum: [int]int, a: [int]int, a₂₃: [int]int, i₂₄: int, sum₂₅: [int]int, i₂₆: int, i₈: int ::
      (  -2147483648 <= N₂₂
        && N₂₂ < 2147483648
        && N₂₂ <= 2147483647 / 4
        && 0 <= i₂₄
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₄
                 ==> i₅ < N₂₂
                  && a₂₃[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₄
                || a₂₃[i₅] == a[i₅])
        && 0 <= i₂₆
        && (forall i₁₃₉: int ::
              (  0 <= i₁₃₉
                && i₁₃₉ < i₂₆
                 ==> i₁₃₉ < N₂₂
                  && sum₂₅[0] == a₂₃[i₁₃₉] + sum[0 := 0][0]))
        && (forall i₁₄₀: int ::
                  0 <= i₁₄₀
                  && i₁₄₀ < i₂₆
                || sum₂₅[0] == sum[0 := 0][0])
        && i₂₆ < N₂₂
         ==> 0 <= i₈
          || i₂₄ < N₂₂
          || N₂₂ <= 0
          || sum₂₅[0 := sum₂₅[0] + a₂₃[i₂₆]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₂₂: int, sum: [int]int, a: [int]int, a₂₃: [int]int, i₂₄: int, sum₂₅: [int]int, i₂₆: int, i₈: int ::
      (  -2147483648 <= N₂₂
        && N₂₂ < 2147483648
        && N₂₂ <= 2147483647 / 4
        && 0 <= i₂₄
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₄
                 ==> i₅ < N₂₂
                  && a₂₃[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₄
                || a₂₃[i₅] == a[i₅])
        && 0 <= i₂₆
        && (forall i₁₄₉: int ::
              (  0 <= i₁₄₉
                && i₁₄₉ < i₂₆
                 ==> i₁₄₉ < N₂₂
                  && sum₂₅[0] == a₂₃[i₁₄₉] + sum[0 := 0][0]))
        && (forall i₁₅₀: int ::
                  0 <= i₁₅₀
                  && i₁₅₀ < i₂₆
                || sum₂₅[0] == sum[0 := 0][0])
        && i₂₆ < N₂₂
         ==> i₈ < i₂₆ + 1
          || i₂₄ < N₂₂
          || N₂₂ <= 0
          || sum₂₅[0 := sum₂₅[0] + a₂₃[i₂₆]][0] == sum[0 := 0][0]));


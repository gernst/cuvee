data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₉: int, sum: [int]int, a: [int]int, a₂₀: [int]int, i₂₁: int, sum₂₂: [int]int, i₂₃: int, i₈: int ::
      (  N₁₉ <= 2147483647 / 4
        && 0 <= i₂₁
        && i₂₁ <= N₁₉
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₁
                 ==> i₅ < N₁₉
                  && a₂₀[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₁
                || a₂₀[i₅] == a[i₅])
        && 0 <= i₂₃
        && i₂₃ <= N₁₉
        && (forall i₁₄₈: int ::
              (  0 <= i₁₄₈
                && i₁₄₈ < i₂₃
                 ==> i₁₄₈ < N₁₉
                  && sum₂₂[0] == a₂₀[i₁₄₈] + sum[0 := 0][0]))
        && (forall i₁₄₉: int ::
                  0 <= i₁₄₉
                  && i₁₄₉ < i₂₃
                || sum₂₂[0] == sum[0 := 0][0])
        && i₂₃ < N₁₉
         ==> 0 <= i₈
          || i₂₁ < N₁₉
          || N₁₉ <= 0
          || sum₂₂[0 := sum₂₂[0] + a₂₀[i₂₃]][0] == sum[0 := 0][0]));

goal (forall N₁₉: int, sum: [int]int, a: [int]int, a₂₀: [int]int, i₂₁: int, sum₂₂: [int]int, i₂₃: int, i₈: int ::
      (  N₁₉ <= 2147483647 / 4
        && 0 <= i₂₁
        && i₂₁ <= N₁₉
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₁
                 ==> i₅ < N₁₉
                  && a₂₀[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₁
                || a₂₀[i₅] == a[i₅])
        && 0 <= i₂₃
        && i₂₃ <= N₁₉
        && (forall i₁₅₈: int ::
              (  0 <= i₁₅₈
                && i₁₅₈ < i₂₃
                 ==> i₁₅₈ < N₁₉
                  && sum₂₂[0] == a₂₀[i₁₅₈] + sum[0 := 0][0]))
        && (forall i₁₅₉: int ::
                  0 <= i₁₅₉
                  && i₁₅₉ < i₂₃
                || sum₂₂[0] == sum[0 := 0][0])
        && i₂₃ < N₁₉
         ==> i₈ < i₂₃ + 1
          || i₂₁ < N₁₉
          || N₁₉ <= 0
          || sum₂₂[0 := sum₂₂[0] + a₂₀[i₂₃]][0] == sum[0 := 0][0]));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₆: int, sum: [int]int, a: [int]int, a₁₇: [int]int, i₁₈: int, sum₁₉: [int]int, i₂₀: int, i₈: int ::
      (  N₁₆ <= 2147483647 / 4
        && 0 <= i₁₈
        && i₁₈ <= N₁₆
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₈
                 ==> i₅ < N₁₆
                  && a₁₇[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₈
                || a₁₇[i₅] == a[i₅])
        && 0 <= i₂₀
        && i₂₀ <= N₁₆
        && (forall i₁₄₃: int ::
              (  0 <= i₁₄₃
                && i₁₄₃ < i₂₀
                 ==> i₁₄₃ < N₁₆
                  && sum₁₉[0] == a₁₇[i₁₄₃] + sum[0 := 0][0]))
        && (forall i₁₄₄: int ::
                  0 <= i₁₄₄
                  && i₁₄₄ < i₂₀
                || sum₁₉[0] == sum[0 := 0][0])
        && i₂₀ < N₁₆
         ==> 0 <= i₈
          || i₁₈ < N₁₆
          || N₁₆ <= 0
          || sum₁₉[0 := sum₁₉[0] + a₁₇[i₂₀]][0] == sum[0 := 0][0]));

goal (forall N₁₆: int, sum: [int]int, a: [int]int, a₁₇: [int]int, i₁₈: int, sum₁₉: [int]int, i₂₀: int, i₈: int ::
      (  N₁₆ <= 2147483647 / 4
        && 0 <= i₁₈
        && i₁₈ <= N₁₆
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₈
                 ==> i₅ < N₁₆
                  && a₁₇[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₈
                || a₁₇[i₅] == a[i₅])
        && 0 <= i₂₀
        && i₂₀ <= N₁₆
        && (forall i₁₅₃: int ::
              (  0 <= i₁₅₃
                && i₁₅₃ < i₂₀
                 ==> i₁₅₃ < N₁₆
                  && sum₁₉[0] == a₁₇[i₁₅₃] + sum[0 := 0][0]))
        && (forall i₁₅₄: int ::
                  0 <= i₁₅₄
                  && i₁₅₄ < i₂₀
                || sum₁₉[0] == sum[0 := 0][0])
        && i₂₀ < N₁₆
         ==> i₈ < i₂₀ + 1
          || i₁₈ < N₁₆
          || N₁₆ <= 0
          || sum₁₉[0 := sum₁₉[0] + a₁₇[i₂₀]][0] == sum[0 := 0][0]));


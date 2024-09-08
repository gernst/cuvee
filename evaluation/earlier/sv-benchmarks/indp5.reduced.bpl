data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₀: int, a: [int]int, sum: [int]int, a₂₁: [int]int, i₂₂: int, a₂₃: [int]int, i₂₄: int, a₂₅: [int]int, i₂₆: int, a₂₇: [int]int, i₂₈: int, sum₂₉: [int]int, i₃₀: int, i₁₇: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> i₅ < N₂₀
                  && a₂₁[i₅] == 1 + i₅ * i₅ + 2 * i₅))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || a₂₁[i₅] == a[i₅])
        && 0 <= i₂₄
        && i₂₄ <= N₂₀
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₂₄
                 ==> i₈ < N₂₀
                  && a₂₃[i₈] == -(i₈ * i₈) + a₂₁[i₈]))
        && (forall i₈: int ::
                  0 <= i₈
                  && i₈ < i₂₄
                || a₂₃[i₈] == a₂₁[i₈])
        && 0 <= i₂₆
        && i₂₆ <= N₂₀
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₆
                 ==> i₁₁ < N₂₀
                  && a₂₅[i₁₁] == -i₁₁ + a₂₃[i₁₁]))
        && (forall i₁₁: int ::
                  0 <= i₁₁
                  && i₁₁ < i₂₆
                || a₂₅[i₁₁] == a₂₃[i₁₁])
        && 0 <= i₂₈
        && i₂₈ <= N₂₀
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₂₈
                 ==> i₁₄ < N₂₀
                  && a₂₇[i₁₄] == a₂₅[i₁₄] + -i₁₄))
        && (forall i₁₄: int ::
                  0 <= i₁₄
                  && i₁₄ < i₂₈
                || a₂₇[i₁₄] == a₂₅[i₁₄])
        && 0 <= i₃₀
        && i₃₀ <= N₂₀
        && (forall i₄₉₃: int ::
              (  0 <= i₄₉₃
                && i₄₉₃ < i₃₀
                 ==> i₄₉₃ < N₂₀
                  && sum₂₉[0] == a₂₇[i₄₉₃] + sum[0 := 0][0]))
        && (forall i₄₉₄: int ::
                  0 <= i₄₉₄
                  && i₄₉₄ < i₃₀
                || sum₂₉[0] == sum[0 := 0][0])
        && i₃₀ < N₂₀
         ==> 0 <= i₁₇
          || i₂₈ < N₂₀
          || i₂₆ < N₂₀
          || i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₉[0 := sum₂₉[0] + a₂₇[i₃₀]][0] == sum[0 := 0][0]));

goal (forall N₂₀: int, a: [int]int, sum: [int]int, a₂₁: [int]int, i₂₂: int, a₂₃: [int]int, i₂₄: int, a₂₅: [int]int, i₂₆: int, a₂₇: [int]int, i₂₈: int, sum₂₉: [int]int, i₃₀: int, i₁₇: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₂
                 ==> i₅ < N₂₀
                  && a₂₁[i₅] == 1 + i₅ * i₅ + 2 * i₅))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₂
                || a₂₁[i₅] == a[i₅])
        && 0 <= i₂₄
        && i₂₄ <= N₂₀
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₂₄
                 ==> i₈ < N₂₀
                  && a₂₃[i₈] == -(i₈ * i₈) + a₂₁[i₈]))
        && (forall i₈: int ::
                  0 <= i₈
                  && i₈ < i₂₄
                || a₂₃[i₈] == a₂₁[i₈])
        && 0 <= i₂₆
        && i₂₆ <= N₂₀
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₆
                 ==> i₁₁ < N₂₀
                  && a₂₅[i₁₁] == -i₁₁ + a₂₃[i₁₁]))
        && (forall i₁₁: int ::
                  0 <= i₁₁
                  && i₁₁ < i₂₆
                || a₂₅[i₁₁] == a₂₃[i₁₁])
        && 0 <= i₂₈
        && i₂₈ <= N₂₀
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₂₈
                 ==> i₁₄ < N₂₀
                  && a₂₇[i₁₄] == a₂₅[i₁₄] + -i₁₄))
        && (forall i₁₄: int ::
                  0 <= i₁₄
                  && i₁₄ < i₂₈
                || a₂₇[i₁₄] == a₂₅[i₁₄])
        && 0 <= i₃₀
        && i₃₀ <= N₂₀
        && (forall i₅₀₉: int ::
              (  0 <= i₅₀₉
                && i₅₀₉ < i₃₀
                 ==> i₅₀₉ < N₂₀
                  && sum₂₉[0] == a₂₇[i₅₀₉] + sum[0 := 0][0]))
        && (forall i₅₁₀: int ::
                  0 <= i₅₁₀
                  && i₅₁₀ < i₃₀
                || sum₂₉[0] == sum[0 := 0][0])
        && i₃₀ < N₂₀
         ==> i₁₇ < i₃₀ + 1
          || i₂₈ < N₂₀
          || i₂₆ < N₂₀
          || i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₉[0 := sum₂₉[0] + a₂₇[i₃₀]][0] == sum[0 := 0][0]));


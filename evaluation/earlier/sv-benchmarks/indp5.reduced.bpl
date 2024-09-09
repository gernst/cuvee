data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₂₀: int, a: [int]int, sum: [int]int, a₂₁: [int]int, i₂₂: int, a₂₃: [int]int, i₂₄: int, a₂₅: [int]int, i₂₆: int, a₂₇: [int]int, i₂₈: int, sum₂₉: [int]int, i₃₀: int, i₁₇: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
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
        && (forall i₄₂₃: int ::
              (  0 <= i₄₂₃
                && i₄₂₃ < i₃₀
                 ==> i₄₂₃ < N₂₀
                  && sum₂₉[0] == a₂₇[i₄₂₃] + sum[0 := 0][0]))
        && (forall i₄₂₄: int ::
                  0 <= i₄₂₄
                  && i₄₂₄ < i₃₀
                || sum₂₉[0] == sum[0 := 0][0])
        && i₃₀ < N₂₀
         ==> 0 <= i₁₇
          || i₂₈ < N₂₀
          || i₂₆ < N₂₀
          || i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₉[0 := sum₂₉[0] + a₂₇[i₃₀]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₂₀: int, a: [int]int, sum: [int]int, a₂₁: [int]int, i₂₂: int, a₂₃: [int]int, i₂₄: int, a₂₅: [int]int, i₂₆: int, a₂₇: [int]int, i₂₈: int, sum₂₉: [int]int, i₃₀: int, i₁₇: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
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
        && (forall i₄₃₉: int ::
              (  0 <= i₄₃₉
                && i₄₃₉ < i₃₀
                 ==> i₄₃₉ < N₂₀
                  && sum₂₉[0] == a₂₇[i₄₃₉] + sum[0 := 0][0]))
        && (forall i₄₄₀: int ::
                  0 <= i₄₄₀
                  && i₄₄₀ < i₃₀
                || sum₂₉[0] == sum[0 := 0][0])
        && i₃₀ < N₂₀
         ==> i₁₇ < i₃₀ + 1
          || i₂₈ < N₂₀
          || i₂₆ < N₂₀
          || i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || sum₂₉[0 := sum₂₉[0] + a₂₇[i₃₀]][0] == sum[0 := 0][0]));


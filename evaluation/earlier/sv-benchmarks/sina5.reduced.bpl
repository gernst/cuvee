data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₂₃: int, sum: [int]int, a: [int]int, b: [int]int, a₂₄: [int]int, i₂₅: int, b₂₆: [int]int, i₂₇: int, sum₂₈: [int]int, i₂₉: int, i₁₂: int ::
      (  N₂₃ <= 2147483647 / 4
        && 0 <= i₂₅
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₅
                 ==> i₆ < N₂₃
                  && a₂₄[i₆] == 1))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₂₅
                || a₂₄[i₆] == a[i₆])
        && 0 <= i₂₇
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₇
                 ==> i₉ < N₂₃
                  && b₂₆[i₉] == 1))
        && (forall i₉: int ::
                  0 <= i₉
                  && i₉ < i₂₇
                || b₂₆[i₉] == b[i₉])
        && 0 <= i₂₉
        && (forall i₂₃₃: int ::
              (  0 <= i₂₃₃
                && i₂₃₃ < i₂₉
                 ==> i₂₃₃ < N₂₃
                  && sum₂₈[0] == a₂₄[i₂₃₃] + sum[0 := 0][0]))
        && (forall i₂₃₄: int ::
                  0 <= i₂₃₄
                  && i₂₃₄ < i₂₉
                || sum₂₈[0] == sum[0 := 0][0])
        && i₂₉ < N₂₃
         ==> 0 <= i₁₂
          || i₂₇ < N₂₃
          || i₂₅ < N₂₃
          || N₂₃ <= 0
          || sum₂₈[0 := sum₂₈[0] + a₂₄[i₂₉]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₂₃: int, sum: [int]int, a: [int]int, b: [int]int, a₂₄: [int]int, i₂₅: int, b₂₆: [int]int, i₂₇: int, sum₂₈: [int]int, i₂₉: int, i₁₂: int ::
      (  N₂₃ <= 2147483647 / 4
        && 0 <= i₂₅
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₅
                 ==> i₆ < N₂₃
                  && a₂₄[i₆] == 1))
        && (forall i₆: int ::
                  0 <= i₆
                  && i₆ < i₂₅
                || a₂₄[i₆] == a[i₆])
        && 0 <= i₂₇
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₇
                 ==> i₉ < N₂₃
                  && b₂₆[i₉] == 1))
        && (forall i₉: int ::
                  0 <= i₉
                  && i₉ < i₂₇
                || b₂₆[i₉] == b[i₉])
        && 0 <= i₂₉
        && (forall i₂₄₆: int ::
              (  0 <= i₂₄₆
                && i₂₄₆ < i₂₉
                 ==> i₂₄₆ < N₂₃
                  && sum₂₈[0] == a₂₄[i₂₄₆] + sum[0 := 0][0]))
        && (forall i₂₄₇: int ::
                  0 <= i₂₄₇
                  && i₂₄₇ < i₂₉
                || sum₂₈[0] == sum[0 := 0][0])
        && i₂₉ < N₂₃
         ==> i₁₂ < i₂₉ + 1
          || i₂₇ < N₂₃
          || i₂₅ < N₂₃
          || N₂₃ <= 0
          || sum₂₈[0 := sum₂₈[0] + a₂₄[i₂₉]][0] == sum[0 := 0][0]));


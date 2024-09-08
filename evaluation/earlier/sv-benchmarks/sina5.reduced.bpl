data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₃: int, sum: [int]int, a: [int]int, b: [int]int, a₂₄: [int]int, i₂₅: int, b₂₆: [int]int, i₂₇: int, sum₂₈: [int]int, i₂₉: int, i₁₂: int ::
      (  N₂₃ <= 2147483647 / 4
        && 0 <= i₂₅
        && i₂₅ <= N₂₃
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
        && i₂₇ <= N₂₃
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
        && i₂₉ <= N₂₃
        && (forall i₂₆₆: int ::
              (  0 <= i₂₆₆
                && i₂₆₆ < i₂₉
                 ==> i₂₆₆ < N₂₃
                  && sum₂₈[0] == a₂₄[i₂₆₆] + sum[0 := 0][0]))
        && (forall i₂₆₇: int ::
                  0 <= i₂₆₇
                  && i₂₆₇ < i₂₉
                || sum₂₈[0] == sum[0 := 0][0])
        && i₂₉ < N₂₃
         ==> 0 <= i₁₂
          || i₂₇ < N₂₃
          || i₂₅ < N₂₃
          || N₂₃ <= 0
          || sum₂₈[0 := sum₂₈[0] + a₂₄[i₂₉]][0] == sum[0 := 0][0]));

goal (forall N₂₃: int, sum: [int]int, a: [int]int, b: [int]int, a₂₄: [int]int, i₂₅: int, b₂₆: [int]int, i₂₇: int, sum₂₈: [int]int, i₂₉: int, i₁₂: int ::
      (  N₂₃ <= 2147483647 / 4
        && 0 <= i₂₅
        && i₂₅ <= N₂₃
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
        && i₂₇ <= N₂₃
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
        && i₂₉ <= N₂₃
        && (forall i₂₇₉: int ::
              (  0 <= i₂₇₉
                && i₂₇₉ < i₂₉
                 ==> i₂₇₉ < N₂₃
                  && sum₂₈[0] == a₂₄[i₂₇₉] + sum[0 := 0][0]))
        && (forall i₂₈₀: int ::
                  0 <= i₂₈₀
                  && i₂₈₀ < i₂₉
                || sum₂₈[0] == sum[0 := 0][0])
        && i₂₉ < N₂₃
         ==> i₁₂ < i₂₉ + 1
          || i₂₇ < N₂₃
          || i₂₅ < N₂₃
          || N₂₃ <= 0
          || sum₂₈[0 := sum₂₈[0] + a₂₄[i₂₉]][0] == sum[0 := 0][0]));


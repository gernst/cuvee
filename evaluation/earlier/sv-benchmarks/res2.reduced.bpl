data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₅: int, sum: [int]int, a: [int]int, a₂₆: [int]int, i₂₇: int, sum₂₈: [int]int, i₂₉: int, i₁₀: int ::
      (  N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
        && i₂₇ <= N₂₅
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₇
                 ==> i₇ < N₂₅
                  && a₂₆[i₇] == 1))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₇
                || a₂₆[i₇] == a[i₇])
        && 0 <= i₂₉
        && i₂₉ <= N₂₅
        && (forall i₁₆₀: int ::
              (  0 <= i₁₆₀
                && i₁₆₀ < i₂₉
                 ==> i₁₆₀ < N₂₅
                  && sum₂₈[0] == sum[0 := 0][0] + a₂₆[i₁₆₀]))
        && (forall i₁₆₁: int ::
                  0 <= i₁₆₁
                  && i₁₆₁ < i₂₉
                || sum₂₈[0] == sum[0 := 0][0])
        && i₂₉ < N₂₅
         ==> 0 <= i₁₀
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || sum₂₈[0 := sum₂₈[0] + a₂₆[i₂₉]][0] == sum[0 := 0][0]));

goal (forall N₂₅: int, sum: [int]int, a: [int]int, a₂₆: [int]int, i₂₇: int, sum₂₈: [int]int, i₂₉: int, i₁₀: int ::
      (  N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
        && i₂₇ <= N₂₅
        && (forall i₇: int ::
              (  0 <= i₇
                && i₇ < i₂₇
                 ==> i₇ < N₂₅
                  && a₂₆[i₇] == 1))
        && (forall i₇: int ::
                  0 <= i₇
                  && i₇ < i₂₇
                || a₂₆[i₇] == a[i₇])
        && 0 <= i₂₉
        && i₂₉ <= N₂₅
        && (forall i₁₇₀: int ::
              (  0 <= i₁₇₀
                && i₁₇₀ < i₂₉
                 ==> i₁₇₀ < N₂₅
                  && sum₂₈[0] == sum[0 := 0][0] + a₂₆[i₁₇₀]))
        && (forall i₁₇₁: int ::
                  0 <= i₁₇₁
                  && i₁₇₁ < i₂₉
                || sum₂₈[0] == sum[0 := 0][0])
        && i₂₉ < N₂₅
         ==> i₁₀ < i₂₉ + 1
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || sum₂₈[0 := sum₂₈[0] + a₂₆[i₂₉]][0] == sum[0 := 0][0]));


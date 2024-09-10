data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₂₅: int, sum: [int]int, a: [int]int, a₂₆: [int]int, i₂₇: int, sum₂₈: [int]int, i₂₉: int, i₈: int ::
      (  N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₇
                 ==> i₅ < N₂₅
                  && a₂₆[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₇
                || a₂₆[i₅] == a[i₅])
        && 0 <= i₂₉
        && (forall i₁₄₆: int ::
              (  0 <= i₁₄₆
                && i₁₄₆ < i₂₉
                 ==> i₁₄₆ < N₂₅
                  && sum₂₈[0] == a₂₆[i₁₄₆] + sum[0 := 0][0]))
        && (forall i₁₄₇: int ::
                  0 <= i₁₄₇
                  && i₁₄₇ < i₂₉
                || sum₂₈[0] == sum[0 := 0][0])
        && i₂₉ < N₂₅
         ==> 0 <= i₈
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || sum₂₈[0 := sum₂₈[0] + a₂₆[i₂₉]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₂₅: int, sum: [int]int, a: [int]int, a₂₆: [int]int, i₂₇: int, sum₂₈: [int]int, i₂₉: int, i₈: int ::
      (  N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₇
                 ==> i₅ < N₂₅
                  && a₂₆[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₇
                || a₂₆[i₅] == a[i₅])
        && 0 <= i₂₉
        && (forall i₁₅₆: int ::
              (  0 <= i₁₅₆
                && i₁₅₆ < i₂₉
                 ==> i₁₅₆ < N₂₅
                  && sum₂₈[0] == a₂₆[i₁₅₆] + sum[0 := 0][0]))
        && (forall i₁₅₇: int ::
                  0 <= i₁₅₇
                  && i₁₅₇ < i₂₉
                || sum₂₈[0] == sum[0 := 0][0])
        && i₂₉ < N₂₅
         ==> i₈ < i₂₉ + 1
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || sum₂₈[0 := sum₂₈[0] + a₂₆[i₂₉]][0] == sum[0 := 0][0]));


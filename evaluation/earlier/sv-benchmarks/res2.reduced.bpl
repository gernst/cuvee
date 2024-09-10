data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₂₅: int, sum: [int]int, a: [int]int, a₂₆: [int]int, i₂₇: int, sum₂₈: [int]int, i₂₉: int, i₁₀: int ::
      (  -2147483648 <= N₂₅
        && N₂₅ < 2147483648
        && N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
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
        && (forall i₁₄₄: int ::
              (  0 <= i₁₄₄
                && i₁₄₄ < i₂₉
                 ==> i₁₄₄ < N₂₅
                  && sum₂₈[0] == sum[0 := 0][0] + a₂₆[i₁₄₄]))
        && (forall i₁₄₅: int ::
                  0 <= i₁₄₅
                  && i₁₄₅ < i₂₉
                || sum₂₈[0] == sum[0 := 0][0])
        && i₂₉ < N₂₅
         ==> 0 <= i₁₀
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || sum₂₈[0 := sum₂₈[0] + a₂₆[i₂₉]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₂₅: int, sum: [int]int, a: [int]int, a₂₆: [int]int, i₂₇: int, sum₂₈: [int]int, i₂₉: int, i₁₀: int ::
      (  -2147483648 <= N₂₅
        && N₂₅ < 2147483648
        && N₂₅ <= 2147483647 / 4
        && 0 <= i₂₇
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
        && (forall i₁₅₄: int ::
              (  0 <= i₁₅₄
                && i₁₅₄ < i₂₉
                 ==> i₁₅₄ < N₂₅
                  && sum₂₈[0] == sum[0 := 0][0] + a₂₆[i₁₅₄]))
        && (forall i₁₅₅: int ::
                  0 <= i₁₅₅
                  && i₁₅₅ < i₂₉
                || sum₂₈[0] == sum[0 := 0][0])
        && i₂₉ < N₂₅
         ==> i₁₀ < i₂₉ + 1
          || i₂₇ < N₂₅
          || N₂₅ <= 0
          || sum₂₈[0 := sum₂₈[0] + a₂₆[i₂₉]][0] == sum[0 := 0][0]));


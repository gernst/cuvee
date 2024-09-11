data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₇: int, sum: [int]int, a: [int]int, a₁₈: [int]int, i₁₉: int, sum₂₀: [int]int, i₂₁: int, i₈: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₉
                 ==> i₅ < N₁₇
                  && a₁₈[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₉
                || a₁₈[i₅] == a[i₅])
        && 0 <= i₂₁
        && (forall i₁₂₈: int ::
              (  0 <= i₁₂₈
                && i₁₂₈ < i₂₁
                 ==> i₁₂₈ < N₁₇
                  && sum₂₀[0] == a₁₈[i₁₂₈] + sum[0 := 0][0]))
        && (forall i₁₂₉: int ::
                  0 <= i₁₂₉
                  && i₁₂₉ < i₂₁
                || sum₂₀[0] == sum[0 := 0][0])
        && i₂₁ < N₁₇
         ==> 0 <= i₈
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || sum₂₀[0 := sum₂₀[0] + a₁₈[i₂₁]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₁₇: int, sum: [int]int, a: [int]int, a₁₈: [int]int, i₁₉: int, sum₂₀: [int]int, i₂₁: int, i₈: int ::
      (  N₁₇ <= 2147483647 / 4
        && 0 <= i₁₉
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₉
                 ==> i₅ < N₁₇
                  && a₁₈[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₉
                || a₁₈[i₅] == a[i₅])
        && 0 <= i₂₁
        && (forall i₁₃₈: int ::
              (  0 <= i₁₃₈
                && i₁₃₈ < i₂₁
                 ==> i₁₃₈ < N₁₇
                  && sum₂₀[0] == a₁₈[i₁₃₈] + sum[0 := 0][0]))
        && (forall i₁₃₉: int ::
                  0 <= i₁₃₉
                  && i₁₃₉ < i₂₁
                || sum₂₀[0] == sum[0 := 0][0])
        && i₂₁ < N₁₇
         ==> i₈ < i₂₁ + 1
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || sum₂₀[0 := sum₂₀[0] + a₁₈[i₂₁]][0] == sum[0 := 0][0]));


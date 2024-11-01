data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₆: int, sum: [int]int, a: [int]int, a₁₇: [int]int, i₁₈: int, sum₁₉: [int]int, i₂₀: int, i₈: int ::
      (  N₁₆ <= 2147483647 / 4
        && 0 <= i₁₈
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
        && (forall i₁₂₅: int ::
              (  0 <= i₁₂₅
                && i₁₂₅ < i₂₀
                 ==> i₁₂₅ < N₁₆
                  && sum₁₉[0] == a₁₇[i₁₂₅] + sum[0 := 0][0]))
        && (forall i₁₂₆: int ::
                  0 <= i₁₂₆
                  && i₁₂₆ < i₂₀
                || sum₁₉[0] == sum[0 := 0][0])
        && i₂₀ < N₁₆
         ==> 0 <= i₈
          || i₁₈ < N₁₆
          || N₁₆ <= 0
          || sum₁₉[0 := sum₁₉[0] + a₁₇[i₂₀]][0] == sum[0 := 0][0]));

goal {:named "invariant forward"} (forall N₁₆: int, sum: [int]int, a: [int]int, a₁₇: [int]int, i₁₈: int, sum₁₉: [int]int, i₂₀: int, i₈: int ::
      (  N₁₆ <= 2147483647 / 4
        && 0 <= i₁₈
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
        && (forall i₁₃₅: int ::
              (  0 <= i₁₃₅
                && i₁₃₅ < i₂₀
                 ==> i₁₃₅ < N₁₆
                  && sum₁₉[0] == a₁₇[i₁₃₅] + sum[0 := 0][0]))
        && (forall i₁₃₆: int ::
                  0 <= i₁₃₆
                  && i₁₃₆ < i₂₀
                || sum₁₉[0] == sum[0 := 0][0])
        && i₂₀ < N₁₆
         ==> i₈ < i₂₀ + 1
          || i₁₈ < N₁₆
          || N₁₆ <= 0
          || sum₁₉[0 := sum₁₉[0] + a₁₇[i₂₀]][0] == sum[0 := 0][0]));


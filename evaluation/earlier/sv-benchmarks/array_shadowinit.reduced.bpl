data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₃: int, a: [int]int, a₁₄: [int]int, i₁₅: int, k₁₆: int, i₁₇: int ::
      (  0 < N₁₃
        && 0 <= i₁₅
        && 0 <= k₁₆
        && i₁₅ <= N₁₃
        && (forall x₇: int, k₆: int ::
              (  x₇ == k₆
                && 0 <= k₆
                && k₆ < k₁₆
                 ==> (exists i₅: int, k₆: int ::
                        i₅ < N₁₃
                        && x₇ == k₆
                        && 0 <= k₆
                        && k₆ < k₁₆
                        && a₁₄[x₇] == k₆)))
        && (forall x₇: int ::
                (exists k₆: int ::
                        x₇ == k₆
                        && 0 <= k₆
                        && k₆ < k₁₆)
                || a₁₄[x₇] == a[x₇])
        && (forall i₅: int, k₆: int ::
              (  i₅ <= i₅
                && k₆ <= k₆
                && 0 <= i₅
                && i₅ < i₁₅
                && 0 <= k₆
                && k₆ < k₁₆
                 ==> i₅ < N₁₃))
        && 0 <= i₁₇
        && i₁₇ <= N₁₃
        && (forall i₁₁: int ::
              (  i₁₁ <= i₁₁
                && 0 <= i₁₁
                && i₁₁ < i₁₇
                 ==> i₁₁ < N₁₃))
        && i₁₇ < N₁₃
         ==> i₁₅ < N₁₃
          || a₁₄[i₁₇] == i₁₇));


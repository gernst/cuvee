data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int, a: [int]int, b: [int]int, a₂₄: [int]int, b₂₅: [int]int, i₂₆: int, a₂₇: [int]int, b₂₈: [int]int, i₂₉: int, i₃₀: int ::
      (  0 < N
        && 1 <= i₂₆
        && i₂₆ <= N
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 1 <= i₁₀
                && i₁₀ < i₂₆
                 ==> (exists j₈: int, k₉: int, i₁₀: int ::
                        j₈ <= k₉
                        && -10000 < k₉
                        && k₉ < 10000
                        && -10000 < j₈
                        && j₈ < 10000
                        && i₁₀ < N
                        && x₁₁ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₆
                        && a₂₄[x₁₁] == k₉)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₆)
                || a₂₄[x₁₁] == a[x₁₁])
        && (forall x₁₂: int, i₁₀: int ::
              (  x₁₂ == i₁₀
                && 1 <= i₁₀
                && i₁₀ < i₂₆
                 ==> (exists j₈: int, k₉: int, i₁₀: int ::
                        j₈ <= k₉
                        && -10000 < k₉
                        && k₉ < 10000
                        && -10000 < j₈
                        && j₈ < 10000
                        && i₁₀ < N
                        && x₁₂ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₆
                        && b₂₅[x₁₂] == j₈)))
        && (forall x₁₂: int ::
                (exists i₁₀: int ::
                        x₁₂ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₆)
                || b₂₅[x₁₂] == b[x₁₂])
        && (forall i₁₀: int ::
              (  1 <= i₁₀
                && i₁₀ < i₂₆
                 ==> i₁₀ < N))
        && 0 <= i₂₉
        && i₂₉ <= N
        && (forall x₁₇: int, i₁₆: int ::
              (  x₁₇ == i₁₆
                && 0 <= i₁₆
                && i₁₆ < i₂₉
                 ==> (exists i₁₆: int ::
                        i₁₆ < N
                        && x₁₇ == i₁₆
                        && 0 <= i₁₆
                        && i₁₆ < i₂₉
                        && a₂₇[x₁₇] == 1 + a₂₄[i₁₆])))
        && (forall x₁₇: int ::
                (exists i₁₆: int ::
                        x₁₇ == i₁₆
                        && 0 <= i₁₆
                        && i₁₆ < i₂₉)
                || a₂₇[x₁₇] == a₂₄[x₁₇])
        && (forall x₁₈: int, i₁₆: int ::
              (  x₁₈ == i₁₆
                && 0 <= i₁₆
                && i₁₆ < i₂₉
                 ==> (exists i₁₆: int ::
                        i₁₆ < N
                        && x₁₈ == i₁₆
                        && 0 <= i₁₆
                        && i₁₆ < i₂₉
                        && b₂₈[x₁₈] == 1 + b₂₅[i₁₆])))
        && (forall x₁₈: int ::
                (exists i₁₆: int ::
                        x₁₈ == i₁₆
                        && 0 <= i₁₆
                        && i₁₆ < i₂₉)
                || b₂₈[x₁₈] == b₂₅[x₁₈])
        && (forall i₁₆: int ::
              (  0 <= i₁₆
                && i₁₆ < i₂₉
                 ==> i₁₆ < N))
        && 1 <= i₃₀
        && i₃₀ <= N
        && (forall i₂₂: int ::
              (  1 <= i₂₂
                && i₂₂ < i₃₀
                 ==> i₂₂ < N))
        && i₃₀ < N
         ==> i₂₉ < N
          || i₂₆ < N
          || b₂₈[i₃₀] <= a₂₇[i₃₀]));


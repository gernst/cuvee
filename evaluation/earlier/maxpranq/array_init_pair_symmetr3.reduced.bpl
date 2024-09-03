data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int, a: [int]int, b: [int]int, c: [int]int, a₂₂: [int]int, b₂₃: [int]int, i₂₄: int, c₂₅: [int]int, i₂₆: int, i₂₇: int ::
      (  0 < N
        && N < 100000
        && 0 < N
        && 1 <= i₂₄
        && i₂₄ <= N
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 1 <= i₁₀
                && i₁₀ < i₂₄
                 ==> (exists x₉: int, i₁₀: int ::
                        x₉ < 100000
                        && -100000 < x₉
                        && i₁₀ < N
                        && x₁₁ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₄
                        && a₂₂[x₁₁] == x₉ + N)))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₄)
                || a₂₂[x₁₁] == a[x₁₁])
        && (forall x₁₂: int, i₁₀: int ::
              (  x₁₂ == i₁₀
                && 1 <= i₁₀
                && i₁₀ < i₂₄
                 ==> (exists x₉: int, i₁₀: int ::
                        x₉ < 100000
                        && -100000 < x₉
                        && i₁₀ < N
                        && x₁₂ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₄
                        && b₂₃[x₁₂] == x₉)))
        && (forall x₁₂: int ::
                (exists i₁₀: int ::
                        x₁₂ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₄)
                || b₂₃[x₁₂] == b[x₁₂])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 1 <= i₁₀
                && i₁₀ < i₂₄
                 ==> i₁₀ < N))
        && 0 <= i₂₆
        && i₂₆ <= N
        && (forall x₁₇: int, i₁₆: int ::
              (  x₁₇ == i₁₆
                && 0 <= i₁₆
                && i₁₆ < i₂₆
                 ==> (exists i₁₆: int ::
                        i₁₆ < N
                        && x₁₇ == i₁₆
                        && 0 <= i₁₆
                        && i₁₆ < i₂₆
                        && c₂₅[x₁₇] == a₂₂[i₁₆] + -b₂₃[i₁₆])))
        && (forall x₁₇: int ::
                (exists i₁₆: int ::
                        x₁₇ == i₁₆
                        && 0 <= i₁₆
                        && i₁₆ < i₂₆)
                || c₂₅[x₁₇] == c[x₁₇])
        && (forall i₁₆: int ::
              (  i₁₆ <= i₁₆
                && 0 <= i₁₆
                && i₁₆ < i₂₆
                 ==> i₁₆ < N))
        && 1 <= i₂₇
        && i₂₇ <= N
        && (forall i₂₀: int ::
              (  i₂₀ <= i₂₀
                && 1 <= i₂₀
                && i₂₀ < i₂₇
                 ==> i₂₀ < N))
        && i₂₇ < N
         ==> i₂₆ < N
          || i₂₄ < N
          || c₂₅[i₂₇] == N));


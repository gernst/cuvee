data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int, a: [int]int, b: [int]int, c: [int]int, a₂₃: [int]int, b₂₄: [int]int, i₂₅: int, c₂₆: [int]int, i₂₇: int, i₂₈: int ::
      (  0 < N
        && N < 1000
        && 1 <= i₂₅
        && i₂₅ <= N
        && (forall x₁₂: int, i₁₁: int ::
              (  x₁₂ == i₁₁
                && 1 <= i₁₁
                && i₁₁ < i₂₅
                 ==> (exists x₉: int, y₁₀: int, i₁₁: int ::
                        x₉ <= y₁₀
                        && i₁₁ < N
                        && x₁₂ == i₁₁
                        && 1 <= i₁₁
                        && i₁₁ < i₂₅
                        && a₂₃[x₁₂] == x₉)))
        && (forall x₁₂: int ::
                (exists i₁₁: int ::
                        x₁₂ == i₁₁
                        && 1 <= i₁₁
                        && i₁₁ < i₂₅)
                || a₂₃[x₁₂] == a[x₁₂])
        && (forall x₁₃: int, i₁₁: int ::
              (  x₁₃ == i₁₁
                && 1 <= i₁₁
                && i₁₁ < i₂₅
                 ==> (exists x₉: int, y₁₀: int, i₁₁: int ::
                        x₉ <= y₁₀
                        && i₁₁ < N
                        && x₁₃ == i₁₁
                        && 1 <= i₁₁
                        && i₁₁ < i₂₅
                        && b₂₄[x₁₃] == y₁₀)))
        && (forall x₁₃: int ::
                (exists i₁₁: int ::
                        x₁₃ == i₁₁
                        && 1 <= i₁₁
                        && i₁₁ < i₂₅)
                || b₂₄[x₁₃] == b[x₁₃])
        && (forall i₁₁: int ::
              (  1 <= i₁₁
                && i₁₁ < i₂₅
                 ==> i₁₁ < N))
        && 0 <= i₂₇
        && i₂₇ <= N
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₂₇
                 ==> (exists i₁₇: int ::
                        i₁₇ < N
                        && x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₂₇
                        && c₂₆[x₁₈] == -a₂₃[i₁₇] + b₂₄[i₁₇])))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₂₇)
                || c₂₆[x₁₈] == c[x₁₈])
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₂₇
                 ==> i₁₇ < N))
        && 1 <= i₂₈
        && i₂₈ <= N
        && (forall i₂₁: int ::
              (  1 <= i₂₁
                && i₂₁ < i₂₈
                 ==> i₂₁ < N))
        && i₂₈ < N
         ==> i₂₇ < N
          || i₂₅ < N
          || 0 <= c₂₆[i₂₈]));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int ::
      0 <= N);

goal (forall N₃₀: int, x: [int]int, ret₃₄: int, i₃₅: int, ret₄₀: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, i₅₀: int ::
      (  1 < N₃₀
        && 0 <= i₃₅
        && i₃₅ <= N₃₀
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < i₃₅
                 ==> i₂ < N₃₀))
        && 0 <= i₄₁
        && i₄₁ <= N₃₀
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < i₄₁
                 ==> i₂ < N₃₀))
        && 0 <= i₄₄
        && i₄₄ <= -1 + N₃₀
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> (exists i₁₇: int ::
                        i₁₇ < -1 + N₃₀
                        && x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₄₄
                        && x₄₃[x₁₈] == x[0 := x[1]][1 := x[0]][1 + i₁₇])))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₄₄)
                || x₄₃[x₁₈] == x[0 := x[1]][1 := x[0]][x₁₈])
        && (forall i₁₇: int ::
              (  i₁₇ <= i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> i₁₇ < -1 + N₃₀))
        && 0 <= i₅₀
        && i₅₀ <= N₃₀
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < i₅₀
                 ==> i₂ < N₃₀))
         ==> ret₃₄ == ret₄₀
          || i₅₀ < N₃₀
          || i₄₄ < N₃₀ - 1
          || i₄₁ < N₃₀
          || i₃₅ < N₃₀));

goal (forall N₃₀: int, x: [int]int, ret₃₄: int, i₃₅: int, i₄₁: int, x₄₃: [int]int, i₄₄: int, ret₄₉: int, i₅₀: int ::
      (  1 < N₃₀
        && 0 <= i₃₅
        && i₃₅ <= N₃₀
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < i₃₅
                 ==> i₂ < N₃₀))
        && 0 <= i₄₁
        && i₄₁ <= N₃₀
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < i₄₁
                 ==> i₂ < N₃₀))
        && 0 <= i₄₄
        && i₄₄ <= -1 + N₃₀
        && (forall x₁₈: int, i₁₇: int ::
              (  x₁₈ == i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> (exists i₁₇: int ::
                        i₁₇ < -1 + N₃₀
                        && x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₄₄
                        && x₄₃[x₁₈] == x[0 := x[1]][1 := x[0]][1 + i₁₇])))
        && (forall x₁₈: int ::
                (exists i₁₇: int ::
                        x₁₈ == i₁₇
                        && 0 <= i₁₇
                        && i₁₇ < i₄₄)
                || x₄₃[x₁₈] == x[0 := x[1]][1 := x[0]][x₁₈])
        && (forall i₁₇: int ::
              (  i₁₇ <= i₁₇
                && 0 <= i₁₇
                && i₁₇ < i₄₄
                 ==> i₁₇ < -1 + N₃₀))
        && 0 <= i₅₀
        && i₅₀ <= N₃₀
        && (forall i₂: int ::
              (  i₂ <= i₂
                && 0 <= i₂
                && i₂ < i₅₀
                 ==> i₂ < N₃₀))
         ==> ret₃₄ == ret₄₉
          || i₅₀ < N₃₀
          || i₄₄ < N₃₀ - 1
          || i₄₁ < N₃₀
          || i₃₅ < N₃₀));


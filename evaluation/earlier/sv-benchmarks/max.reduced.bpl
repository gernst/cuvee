data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N: int ::
      0 <= N);

goal (forall N₃₃: int, x: [int]int, ret₃₇: int, i₃₈: int, ret₄₃: int, i₄₄: int, x₄₆: [int]int, i₄₇: int, i₅₃: int ::
      (  1 < N₃₃
        && 0 <= i₃₈
        && i₃₈ <= N₃₃
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₃₈
                 ==> i₅ < N₃₃))
        && 0 <= i₄₄
        && i₄₄ <= N₃₃
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₄₄
                 ==> i₅ < N₃₃))
        && 0 <= i₄₇
        && i₄₇ <= -1 + N₃₃
        && (forall x₂₁: int, i₂₀: int ::
              (  x₂₁ == i₂₀
                && 0 <= i₂₀
                && i₂₀ < i₄₇
                 ==> (exists i₂₀: int ::
                        i₂₀ < -1 + N₃₃
                        && x₂₁ == i₂₀
                        && 0 <= i₂₀
                        && i₂₀ < i₄₇
                        && x₄₆[x₂₁] == x[0 := x[1]][1 := x[0]][1 + i₂₀])))
        && (forall x₂₁: int ::
                (exists i₂₀: int ::
                        x₂₁ == i₂₀
                        && 0 <= i₂₀
                        && i₂₀ < i₄₇)
                || x₄₆[x₂₁] == x[0 := x[1]][1 := x[0]][x₂₁])
        && (forall i₂₀: int ::
              (  i₂₀ <= i₂₀
                && 0 <= i₂₀
                && i₂₀ < i₄₇
                 ==> i₂₀ < -1 + N₃₃))
        && 0 <= i₅₃
        && i₅₃ <= N₃₃
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₅₃
                 ==> i₅ < N₃₃))
         ==> ret₃₇ == ret₄₃
          || i₅₃ < N₃₃
          || i₄₇ < N₃₃ - 1
          || i₄₄ < N₃₃
          || i₃₈ < N₃₃));

goal (forall N₃₃: int, x: [int]int, ret₃₇: int, i₃₈: int, i₄₄: int, x₄₆: [int]int, i₄₇: int, ret₅₂: int, i₅₃: int ::
      (  1 < N₃₃
        && 0 <= i₃₈
        && i₃₈ <= N₃₃
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₃₈
                 ==> i₅ < N₃₃))
        && 0 <= i₄₄
        && i₄₄ <= N₃₃
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₄₄
                 ==> i₅ < N₃₃))
        && 0 <= i₄₇
        && i₄₇ <= -1 + N₃₃
        && (forall x₂₁: int, i₂₀: int ::
              (  x₂₁ == i₂₀
                && 0 <= i₂₀
                && i₂₀ < i₄₇
                 ==> (exists i₂₀: int ::
                        i₂₀ < -1 + N₃₃
                        && x₂₁ == i₂₀
                        && 0 <= i₂₀
                        && i₂₀ < i₄₇
                        && x₄₆[x₂₁] == x[0 := x[1]][1 := x[0]][1 + i₂₀])))
        && (forall x₂₁: int ::
                (exists i₂₀: int ::
                        x₂₁ == i₂₀
                        && 0 <= i₂₀
                        && i₂₀ < i₄₇)
                || x₄₆[x₂₁] == x[0 := x[1]][1 := x[0]][x₂₁])
        && (forall i₂₀: int ::
              (  i₂₀ <= i₂₀
                && 0 <= i₂₀
                && i₂₀ < i₄₇
                 ==> i₂₀ < -1 + N₃₃))
        && 0 <= i₅₃
        && i₅₃ <= N₃₃
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₅₃
                 ==> i₅ < N₃₃))
         ==> ret₃₇ == ret₅₂
          || i₅₃ < N₃₃
          || i₄₇ < N₃₃ - 1
          || i₄₄ < N₃₃
          || i₃₈ < N₃₃));


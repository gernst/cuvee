data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₃: int, b: [int]int, b₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && (forall i₅₀: int ::
              (  1 <= i₅₀
                && i₅₀ < i₁₅
                 ==> i₅₀ < N₁₃
                  && b₁₄[i₅₀] == 2 + b[0 := 1][-1 + i₅₀]))
        && (forall i₅₁: int ::
                  1 <= i₅₁
                  && i₅₁ < i₁₅
                || b₁₄[i₅₁] == b[0 := 1][i₅₁])
        && i₁₅ < N₁₃
        && 1 <= i₅
        && i₅ < i₁₅ + 1
         ==> N₁₃ <= 0
          || b₁₄[i₁₅ := b₁₄[i₁₅ - 1] + 2][i₅] == 2 + b[0 := 1][-1 + i₅]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₅
                 ==> i₅ < N₁₃
                  && b₁₄[i₅] == 2 + b[0 := 1][-1 + i₅]))
        && (forall i₅: int ::
                  1 <= i₅
                  && i₅ < i₁₅
                || b₁₄[i₅] == b[0 := 1][i₅])
        && 1 <= i₁₇
        && (forall i₁₁₂: int ::
              (  1 <= i₁₁₂
                && i₁₁₂ < i₁₇
                 ==> i₁₁₂ < N₁₃
                  && a₁₆[i₁₁₂] == 2 + a[0 := 1][-1 + i₁₁₂] + b₁₄[-1 + i₁₁₂]))
        && (forall i₁₁₃: int ::
                  1 <= i₁₁₃
                  && i₁₁₃ < i₁₇
                || a₁₆[i₁₁₃] == a[0 := 1][i₁₁₃])
        && i₁₇ < N₁₃
        && 1 <= i₈
        && i₈ < i₁₇ + 1
         ==> i₁₅ < N₁₃
          || N₁₃ <= 0
          || a₁₆[i₁₇ := a₁₆[i₁₇ - 1] + b₁₄[i₁₇ - 1] + 2][i₈] == 2 + a[0 := 1][-1 + i₈] + b₁₄[-1 + i₈]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₁₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₅
                 ==> i₅ < N₁₃
                  && b₁₄[i₅] == 2 + b[0 := 1][-1 + i₅]))
        && (forall i₅: int ::
                  1 <= i₅
                  && i₅ < i₁₅
                || b₁₄[i₅] == b[0 := 1][i₅])
        && 1 <= i₁₇
        && (forall i₈: int ::
              (  1 <= i₈
                && i₈ < i₁₇
                 ==> i₈ < N₁₃
                  && a₁₆[i₈] == 2 + a[0 := 1][-1 + i₈] + b₁₄[-1 + i₈]))
        && (forall i₈: int ::
                  1 <= i₈
                  && i₈ < i₁₇
                || a₁₆[i₈] == a[0 := 1][i₈])
        && 0 <= i₁₈
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₁₈
                 ==> i₁₁ < N₁₃))
        && i₁₈ < N₁₃
         ==> i₁₇ < N₁₃
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || a₁₆[i₁₈] == (i₁₈ + 1) * (i₁₈ + 1)));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, a₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && (forall i₅₀: int ::
              (  1 <= i₅₀
                && i₅₀ < i₁₅
                 ==> i₅₀ < N₁₃
                  && a₁₄[i₅₀] == 6 + a[0 := 6][-1 + i₅₀]))
        && (forall i₅₁: int ::
                  1 <= i₅₁
                  && i₅₁ < i₁₅
                || a₁₄[i₅₁] == a[0 := 6][i₅₁])
        && i₁₅ < N₁₃
        && 1 <= i₅
        && i₅ < i₁₅ + 1
         ==> N₁₃ <= 0
          || a₁₄[i₁₅ := a₁₄[i₁₅ - 1] + 6][i₅] == 6 + a[0 := 6][-1 + i₅]));

goal {:named "invariant forward"} (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₅
                 ==> i₅ < N₁₃
                  && a₁₄[i₅] == 6 + a[0 := 6][-1 + i₅]))
        && (forall i₅: int ::
                  1 <= i₅
                  && i₅ < i₁₅
                || a₁₄[i₅] == a[0 := 6][i₅])
        && 1 <= i₁₇
        && (forall i₁₁₂: int ::
              (  1 <= i₁₁₂
                && i₁₁₂ < i₁₇
                 ==> i₁₁₂ < N₁₃
                  && b₁₆[i₁₁₂] == b[0 := 1][-1 + i₁₁₂] + a₁₄[-1 + i₁₁₂]))
        && (forall i₁₁₃: int ::
                  1 <= i₁₁₃
                  && i₁₁₃ < i₁₇
                || b₁₆[i₁₁₃] == b[0 := 1][i₁₁₃])
        && i₁₇ < N₁₃
        && 1 <= i₈
        && i₈ < i₁₇ + 1
         ==> i₁₅ < N₁₃
          || N₁₃ <= 0
          || b₁₆[i₁₇ := b₁₆[i₁₇ - 1] + a₁₄[i₁₇ - 1]][i₈] == b[0 := 1][-1 + i₈] + a₁₄[-1 + i₈]));

goal {:named "assert"} (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₁₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₅
                 ==> i₅ < N₁₃
                  && a₁₄[i₅] == 6 + a[0 := 6][-1 + i₅]))
        && (forall i₅: int ::
                  1 <= i₅
                  && i₅ < i₁₅
                || a₁₄[i₅] == a[0 := 6][i₅])
        && 1 <= i₁₇
        && (forall i₈: int ::
              (  1 <= i₈
                && i₈ < i₁₇
                 ==> i₈ < N₁₃
                  && b₁₆[i₈] == b[0 := 1][-1 + i₈] + a₁₄[-1 + i₈]))
        && (forall i₈: int ::
                  1 <= i₈
                  && i₈ < i₁₇
                || b₁₆[i₈] == b[0 := 1][i₈])
        && 0 <= i₁₈
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₁₈
                 ==> i₁₁ < N₁₃))
        && i₁₈ < N₁₃
         ==> i₁₇ < N₁₃
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || b₁₆[i₁₈] == 3 * i₁₈ * i₁₈ + 3 * i₁₈ + 1));


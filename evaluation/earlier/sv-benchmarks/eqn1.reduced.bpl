data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₃: int, a: [int]int, a₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && i₁₅ <= N₁₃
        && (forall i₅₅: int ::
              (  1 <= i₅₅
                && i₅₅ < i₁₅
                 ==> i₅₅ < N₁₃
                  && a₁₄[i₅₅] == 2 + a[0 := 2][-1 + i₅₅]))
        && (forall i₅₆: int ::
                  1 <= i₅₆
                  && i₅₆ < i₁₅
                || a₁₄[i₅₆] == a[0 := 2][i₅₆])
        && i₁₅ < N₁₃
        && 1 <= i₅
        && i₅ < i₁₅ + 1
         ==> N₁₃ <= 0
          || a₁₄[i₁₅ := a₁₄[i₁₅ - 1] + 2][i₅] == 2 + a[0 := 2][-1 + i₅]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && i₁₅ <= N₁₃
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₅
                 ==> i₅ < N₁₃
                  && a₁₄[i₅] == 2 + a[0 := 2][-1 + i₅]))
        && (forall i₅: int ::
                  1 <= i₅
                  && i₅ < i₁₅
                || a₁₄[i₅] == a[0 := 2][i₅])
        && 1 <= i₁₇
        && i₁₇ <= N₁₃
        && (forall i₁₂₈: int ::
              (  1 <= i₁₂₈
                && i₁₂₈ < i₁₇
                 ==> i₁₂₈ < N₁₃
                  && b₁₆[i₁₂₈] == b[0 := 1][-1 + i₁₂₈] + a₁₄[-1 + i₁₂₈]))
        && (forall i₁₂₉: int ::
                  1 <= i₁₂₉
                  && i₁₂₉ < i₁₇
                || b₁₆[i₁₂₉] == b[0 := 1][i₁₂₉])
        && i₁₇ < N₁₃
        && 1 <= i₈
        && i₈ < i₁₇ + 1
         ==> i₁₅ < N₁₃
          || N₁₃ <= 0
          || b₁₆[i₁₇ := b₁₆[i₁₇ - 1] + a₁₄[i₁₇ - 1]][i₈] == b[0 := 1][-1 + i₈] + a₁₄[-1 + i₈]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, a₁₄: [int]int, i₁₅: int, b₁₆: [int]int, i₁₇: int, i₁₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && i₁₅ <= N₁₃
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₅
                 ==> i₅ < N₁₃
                  && a₁₄[i₅] == 2 + a[0 := 2][-1 + i₅]))
        && (forall i₅: int ::
                  1 <= i₅
                  && i₅ < i₁₅
                || a₁₄[i₅] == a[0 := 2][i₅])
        && 1 <= i₁₇
        && i₁₇ <= N₁₃
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
        && i₁₈ <= N₁₃
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₁₈
                 ==> i₁₁ < N₁₃))
        && i₁₈ < N₁₃
         ==> i₁₇ < N₁₃
          || i₁₅ < N₁₃
          || N₁₃ <= 0
          || b₁₆[i₁₈] == i₁₈ * i₁₈ + i₁₈ + 1));


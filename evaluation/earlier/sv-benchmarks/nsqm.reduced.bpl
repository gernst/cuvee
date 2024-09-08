data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₃: int, b: [int]int, b₁₄: [int]int, i₁₅: int, i₅: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && i₁₅ <= N₁₃
        && (forall i₅₅: int ::
              (  1 <= i₅₅
                && i₅₅ < i₁₅
                 ==> i₅₅ < N₁₃
                  && b₁₄[i₅₅] == 2 + b[0 := 1][-1 + i₅₅]))
        && (forall i₅₆: int ::
                  1 <= i₅₆
                  && i₅₆ < i₁₅
                || b₁₄[i₅₆] == b[0 := 1][i₅₆])
        && i₁₅ < N₁₃
        && 1 <= i₅
        && i₅ < i₁₅ + 1
         ==> N₁₃ <= 0
          || b₁₄[i₁₅ := b₁₄[i₁₅ - 1] + 2][i₅] == 2 + b[0 := 1][-1 + i₅]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && i₁₅ <= N₁₃
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
        && i₁₇ <= N₁₃
        && (forall i₁₂₈: int ::
              (  1 <= i₁₂₈
                && i₁₂₈ < i₁₇
                 ==> i₁₂₈ < N₁₃
                  && a₁₆[i₁₂₈] == 2 + a[0 := N₁₃ + 1][-1 + i₁₂₈] + b₁₄[-1 + i₁₂₈]))
        && (forall i₁₂₉: int ::
                  1 <= i₁₂₉
                  && i₁₂₉ < i₁₇
                || a₁₆[i₁₂₉] == a[0 := N₁₃ + 1][i₁₂₉])
        && i₁₇ < N₁₃
        && 1 <= i₈
        && i₈ < i₁₇ + 1
         ==> i₁₅ < N₁₃
          || N₁₃ <= 0
          || a₁₆[i₁₇ := a₁₆[i₁₇ - 1] + b₁₄[i₁₇ - 1] + 2][i₈] == 2 + a[0 := N₁₃ + 1][-1 + i₈] + b₁₄[-1 + i₈]));

goal (forall N₁₃: int, a: [int]int, b: [int]int, b₁₄: [int]int, i₁₅: int, a₁₆: [int]int, i₁₇: int, i₁₈: int ::
      (  N₁₃ <= 2147483647 / 4
        && 1 <= i₁₅
        && i₁₅ <= N₁₃
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
        && i₁₇ <= N₁₃
        && (forall i₈: int ::
              (  1 <= i₈
                && i₈ < i₁₇
                 ==> i₈ < N₁₃
                  && a₁₆[i₈] == 2 + a[0 := N₁₃ + 1][-1 + i₈] + b₁₄[-1 + i₈]))
        && (forall i₈: int ::
                  1 <= i₈
                  && i₈ < i₁₇
                || a₁₆[i₈] == a[0 := N₁₃ + 1][i₈])
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
          || a₁₆[i₁₈] == N₁₃ + (i₁₈ + 1) * (i₁₈ + 1)));


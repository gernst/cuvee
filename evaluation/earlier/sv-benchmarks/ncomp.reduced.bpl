data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, a₁₈: [int]int, i₁₉: int, i₆: int ::
      (  N₁₇ <= 2147483647 / 4
        && 1 <= i₁₉
        && (forall i₅₈: int ::
              (  1 <= i₅₈
                && i₅₈ < i₁₉
                 ==> i₅₈ < N₁₇
                  && a₁₈[i₅₈] == 6 + a[0 := 6][-1 + i₅₈]))
        && (forall i₅₉: int ::
                  1 <= i₅₉
                  && i₅₉ < i₁₉
                || a₁₈[i₅₉] == a[0 := 6][i₅₉])
        && i₁₉ < N₁₇
        && 1 <= i₆
        && i₆ < i₁₉ + 1
         ==> N₁₇ <= 0
          || a₁₈[i₁₉ := a₁₈[i₁₉ - 1] + 6][i₆] == 6 + a[0 := 6][-1 + i₆]));

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, b: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, i₉: int ::
      (  N₁₇ <= 2147483647 / 4
        && 1 <= i₁₉
        && (forall i₆: int ::
              (  1 <= i₆
                && i₆ < i₁₉
                 ==> i₆ < N₁₇
                  && a₁₈[i₆] == 6 + a[0 := 6][-1 + i₆]))
        && (forall i₆: int ::
                  1 <= i₆
                  && i₆ < i₁₉
                || a₁₈[i₆] == a[0 := 6][i₆])
        && 1 <= i₂₁
        && (forall i₁₂₀: int ::
              (  1 <= i₁₂₀
                && i₁₂₀ < i₂₁
                 ==> i₁₂₀ < N₁₇
                  && b₂₀[i₁₂₀] == b[0 := 1][-1 + i₁₂₀] + a₁₈[-1 + i₁₂₀]))
        && (forall i₁₂₁: int ::
                  1 <= i₁₂₁
                  && i₁₂₁ < i₂₁
                || b₂₀[i₁₂₁] == b[0 := 1][i₁₂₁])
        && i₂₁ < N₁₇
        && 1 <= i₉
        && i₉ < i₂₁ + 1
         ==> i₁₉ < N₁₇
          || N₁₇ <= 0
          || b₂₀[i₂₁ := b₂₀[i₂₁ - 1] + a₁₈[i₂₁ - 1]][i₉] == b[0 := 1][-1 + i₉] + a₁₈[-1 + i₉]));

goal {:named "invariant forward"} (forall N₁₇: int, a: [int]int, b: [int]int, c: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, c₂₂: [int]int, i₂₃: int, i₁₂: int ::
      (  N₁₇ <= 2147483647 / 4
        && 1 <= i₁₉
        && (forall i₆: int ::
              (  1 <= i₆
                && i₆ < i₁₉
                 ==> i₆ < N₁₇
                  && a₁₈[i₆] == 6 + a[0 := 6][-1 + i₆]))
        && (forall i₆: int ::
                  1 <= i₆
                  && i₆ < i₁₉
                || a₁₈[i₆] == a[0 := 6][i₆])
        && 1 <= i₂₁
        && (forall i₉: int ::
              (  1 <= i₉
                && i₉ < i₂₁
                 ==> i₉ < N₁₇
                  && b₂₀[i₉] == b[0 := 1][-1 + i₉] + a₁₈[-1 + i₉]))
        && (forall i₉: int ::
                  1 <= i₉
                  && i₉ < i₂₁
                || b₂₀[i₉] == b[0 := 1][i₉])
        && 1 <= i₂₃
        && (forall i₂₁₂: int ::
              (  1 <= i₂₁₂
                && i₂₁₂ < i₂₃
                 ==> i₂₁₂ < N₁₇
                  && c₂₂[i₂₁₂] == c[0 := N₁₇][-1 + i₂₁₂] + b₂₀[-1 + i₂₁₂]))
        && (forall i₂₁₃: int ::
                  1 <= i₂₁₃
                  && i₂₁₃ < i₂₃
                || c₂₂[i₂₁₃] == c[0 := N₁₇][i₂₁₃])
        && i₂₃ < N₁₇
        && 1 <= i₁₂
        && i₁₂ < i₂₃ + 1
         ==> i₂₁ < N₁₇
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || c₂₂[i₂₃ := c₂₂[i₂₃ - 1] + b₂₀[i₂₃ - 1]][i₁₂] == c[0 := N₁₇][-1 + i₁₂] + b₂₀[-1 + i₁₂]));

goal {:named "assert"} (forall N₁₇: int, a: [int]int, b: [int]int, c: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, c₂₂: [int]int, i₂₃: int, i₂₄: int ::
      (  N₁₇ <= 2147483647 / 4
        && 1 <= i₁₉
        && (forall i₆: int ::
              (  1 <= i₆
                && i₆ < i₁₉
                 ==> i₆ < N₁₇
                  && a₁₈[i₆] == 6 + a[0 := 6][-1 + i₆]))
        && (forall i₆: int ::
                  1 <= i₆
                  && i₆ < i₁₉
                || a₁₈[i₆] == a[0 := 6][i₆])
        && 1 <= i₂₁
        && (forall i₉: int ::
              (  1 <= i₉
                && i₉ < i₂₁
                 ==> i₉ < N₁₇
                  && b₂₀[i₉] == b[0 := 1][-1 + i₉] + a₁₈[-1 + i₉]))
        && (forall i₉: int ::
                  1 <= i₉
                  && i₉ < i₂₁
                || b₂₀[i₉] == b[0 := 1][i₉])
        && 1 <= i₂₃
        && (forall i₁₂: int ::
              (  1 <= i₁₂
                && i₁₂ < i₂₃
                 ==> i₁₂ < N₁₇
                  && c₂₂[i₁₂] == c[0 := N₁₇][-1 + i₁₂] + b₂₀[-1 + i₁₂]))
        && (forall i₁₂: int ::
                  1 <= i₁₂
                  && i₁₂ < i₂₃
                || c₂₂[i₁₂] == c[0 := N₁₇][i₁₂])
        && 0 <= i₂₄
        && (forall i₁₅: int ::
              (  0 <= i₁₅
                && i₁₅ < i₂₄
                 ==> i₁₅ < N₁₇))
        && i₂₄ < N₁₇
         ==> i₂₃ < N₁₇
          || i₂₁ < N₁₇
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || c₂₂[i₂₄] == N₁₇ + i₂₄ * i₂₄ * i₂₄));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₇: int, a: [int]int, a₁₈: [int]int, i₁₉: int, i₆: int ::
      (  N₁₇ <= 2147483647 / 4
        && 1 <= i₁₉
        && i₁₉ <= N₁₇
        && (forall i₆₃: int ::
              (  1 <= i₆₃
                && i₆₃ < i₁₉
                 ==> i₆₃ < N₁₇
                  && a₁₈[i₆₃] == 6 + a[0 := 6][-1 + i₆₃]))
        && (forall i₆₄: int ::
                  1 <= i₆₄
                  && i₆₄ < i₁₉
                || a₁₈[i₆₄] == a[0 := 6][i₆₄])
        && i₁₉ < N₁₇
        && 1 <= i₆
        && i₆ < i₁₉ + 1
         ==> N₁₇ <= 0
          || a₁₈[i₁₉ := a₁₈[i₁₉ - 1] + 6][i₆] == 6 + a[0 := 6][-1 + i₆]));

goal (forall N₁₇: int, a: [int]int, b: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, i₉: int ::
      (  N₁₇ <= 2147483647 / 4
        && 1 <= i₁₉
        && i₁₉ <= N₁₇
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
        && i₂₁ <= N₁₇
        && (forall i₁₃₆: int ::
              (  1 <= i₁₃₆
                && i₁₃₆ < i₂₁
                 ==> i₁₃₆ < N₁₇
                  && b₂₀[i₁₃₆] == b[0 := 1][-1 + i₁₃₆] + a₁₈[-1 + i₁₃₆]))
        && (forall i₁₃₇: int ::
                  1 <= i₁₃₇
                  && i₁₃₇ < i₂₁
                || b₂₀[i₁₃₇] == b[0 := 1][i₁₃₇])
        && i₂₁ < N₁₇
        && 1 <= i₉
        && i₉ < i₂₁ + 1
         ==> i₁₉ < N₁₇
          || N₁₇ <= 0
          || b₂₀[i₂₁ := b₂₀[i₂₁ - 1] + a₁₈[i₂₁ - 1]][i₉] == b[0 := 1][-1 + i₉] + a₁₈[-1 + i₉]));

goal (forall N₁₇: int, a: [int]int, b: [int]int, c: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, c₂₂: [int]int, i₂₃: int, i₁₂: int ::
      (  N₁₇ <= 2147483647 / 4
        && 1 <= i₁₉
        && i₁₉ <= N₁₇
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
        && i₂₁ <= N₁₇
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
        && i₂₃ <= N₁₇
        && (forall i₂₄₅: int ::
              (  1 <= i₂₄₅
                && i₂₄₅ < i₂₃
                 ==> i₂₄₅ < N₁₇
                  && c₂₂[i₂₄₅] == c[0 := N₁₇][-1 + i₂₄₅] + b₂₀[-1 + i₂₄₅]))
        && (forall i₂₄₆: int ::
                  1 <= i₂₄₆
                  && i₂₄₆ < i₂₃
                || c₂₂[i₂₄₆] == c[0 := N₁₇][i₂₄₆])
        && i₂₃ < N₁₇
        && 1 <= i₁₂
        && i₁₂ < i₂₃ + 1
         ==> i₂₁ < N₁₇
          || i₁₉ < N₁₇
          || N₁₇ <= 0
          || c₂₂[i₂₃ := c₂₂[i₂₃ - 1] + b₂₀[i₂₃ - 1]][i₁₂] == c[0 := N₁₇][-1 + i₁₂] + b₂₀[-1 + i₁₂]));

goal (forall N₁₇: int, a: [int]int, b: [int]int, c: [int]int, a₁₈: [int]int, i₁₉: int, b₂₀: [int]int, i₂₁: int, c₂₂: [int]int, i₂₃: int, i₂₄: int ::
      (  N₁₇ <= 2147483647 / 4
        && 1 <= i₁₉
        && i₁₉ <= N₁₇
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
        && i₂₁ <= N₁₇
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
        && i₂₃ <= N₁₇
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
        && i₂₄ <= N₁₇
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


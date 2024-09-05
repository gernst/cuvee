data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₅: int, a: [int]int, a₁₆: [int]int, i₁₇: int, x₆: int, i₅: int ::
      (  N₁₅ <= 2147483647 / 4
        && 1 <= i₁₇
        && i₁₇ <= N₁₅
        && (forall x₅₁: int, i₅₂: int ::
              (  x₅₁ == i₅₂
                && 1 <= i₅₂
                && i₅₂ < i₁₇
                 ==> (exists i₅₃: int ::
                        i₅₃ < N₁₅
                        && x₅₁ == i₅₃
                        && 1 <= i₅₃
                        && i₅₃ < i₁₇
                        && a₁₆[x₅₁] == 6 + a[0 := 6][-1 + i₅₃])))
        && (forall x₅₄: int ::
                (exists i₅₅: int ::
                        x₅₄ == i₅₅
                        && 1 <= i₅₅
                        && i₅₅ < i₁₇)
                || a₁₆[x₅₄] == a[0 := 6][x₅₄])
        && (forall i₅₆: int ::
              (  1 <= i₅₆
                && i₅₆ < i₁₇
                 ==> i₅₆ < N₁₅))
        && i₁₇ < N₁₅
        && x₆ == i₅
        && 1 <= i₅
        && i₅ < i₁₇ + 1
         ==> N₁₅ <= 0
          || (exists i₅₇: int ::
                  i₅₇ < N₁₅
                  && x₆ == i₅₇
                  && 1 <= i₅₇
                  && i₅₇ < i₁₇ + 1
                  && a₁₆[i₁₇ := a₁₆[i₁₇ - 1] + 6][x₆] == 6 + a[0 := 6][-1 + i₅₇])));

goal (forall N₁₅: int, a: [int]int, b: [int]int, a₁₆: [int]int, i₁₇: int, b₁₈: [int]int, i₁₉: int, x₁₀: int, i₉: int ::
      (  N₁₅ <= 2147483647 / 4
        && 1 <= i₁₇
        && i₁₇ <= N₁₅
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 1 <= i₅
                && i₅ < i₁₇
                 ==> (exists i₅: int ::
                        i₅ < N₁₅
                        && x₆ == i₅
                        && 1 <= i₅
                        && i₅ < i₁₇
                        && a₁₆[x₆] == 6 + a[0 := 6][-1 + i₅])))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 1 <= i₅
                        && i₅ < i₁₇)
                || a₁₆[x₆] == a[0 := 6][x₆])
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₇
                 ==> i₅ < N₁₅))
        && 1 <= i₁₉
        && i₁₉ <= N₁₅
        && (forall x₁₁₈: int, i₁₁₇: int ::
              (  x₁₁₈ == i₁₁₇
                && 1 <= i₁₁₇
                && i₁₁₇ < i₁₉
                 ==> (exists i₁₁₉: int ::
                        i₁₁₉ < N₁₅
                        && x₁₁₈ == i₁₁₉
                        && 1 <= i₁₁₉
                        && i₁₁₉ < i₁₉
                        && b₁₈[x₁₁₈] == b[0 := 1][-1 + i₁₁₉] + a₁₆[-1 + i₁₁₉])))
        && (forall x₁₂₀: int ::
                (exists i₁₂₁: int ::
                        x₁₂₀ == i₁₂₁
                        && 1 <= i₁₂₁
                        && i₁₂₁ < i₁₉)
                || b₁₈[x₁₂₀] == b[0 := 1][x₁₂₀])
        && (forall i₁₂₂: int ::
              (  1 <= i₁₂₂
                && i₁₂₂ < i₁₉
                 ==> i₁₂₂ < N₁₅))
        && i₁₉ < N₁₅
        && x₁₀ == i₉
        && 1 <= i₉
        && i₉ < i₁₉ + 1
         ==> i₁₇ < N₁₅
          || N₁₅ <= 0
          || (exists i₁₂₃: int ::
                  i₁₂₃ < N₁₅
                  && x₁₀ == i₁₂₃
                  && 1 <= i₁₂₃
                  && i₁₂₃ < i₁₉ + 1
                  && b₁₈[i₁₉ := b₁₈[i₁₉ - 1] + a₁₆[i₁₉ - 1]][x₁₀] == b[0 := 1][-1 + i₁₂₃] + a₁₆[-1 + i₁₂₃])));

goal (forall N₁₅: int, a: [int]int, b: [int]int, a₁₆: [int]int, i₁₇: int, b₁₈: [int]int, i₁₉: int, i₂₀: int ::
      (  N₁₅ <= 2147483647 / 4
        && 1 <= i₁₇
        && i₁₇ <= N₁₅
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 1 <= i₅
                && i₅ < i₁₇
                 ==> (exists i₅: int ::
                        i₅ < N₁₅
                        && x₆ == i₅
                        && 1 <= i₅
                        && i₅ < i₁₇
                        && a₁₆[x₆] == 6 + a[0 := 6][-1 + i₅])))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 1 <= i₅
                        && i₅ < i₁₇)
                || a₁₆[x₆] == a[0 := 6][x₆])
        && (forall i₅: int ::
              (  1 <= i₅
                && i₅ < i₁₇
                 ==> i₅ < N₁₅))
        && 1 <= i₁₉
        && i₁₉ <= N₁₅
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == i₉
                && 1 <= i₉
                && i₉ < i₁₉
                 ==> (exists i₉: int ::
                        i₉ < N₁₅
                        && x₁₀ == i₉
                        && 1 <= i₉
                        && i₉ < i₁₉
                        && b₁₈[x₁₀] == b[0 := 1][-1 + i₉] + a₁₆[-1 + i₉])))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == i₉
                        && 1 <= i₉
                        && i₉ < i₁₉)
                || b₁₈[x₁₀] == b[0 := 1][x₁₀])
        && (forall i₉: int ::
              (  1 <= i₉
                && i₉ < i₁₉
                 ==> i₉ < N₁₅))
        && 0 <= i₂₀
        && i₂₀ <= N₁₅
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₀
                 ==> i₁₃ < N₁₅))
        && i₂₀ < N₁₅
         ==> i₁₉ < N₁₅
          || i₁₇ < N₁₅
          || N₁₅ <= 0
          || b₁₈[i₂₀] == 3 * i₂₀ * i₂₀ + 3 * i₂₀ + 1));


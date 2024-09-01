data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₀: int, a: [int]int, a₂₁: [int]int, i₂₂: int, x₇: int, i₆: int ::
      (  N₂₀ <= 2147483647 / 4
        && 1 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall x₆₁: int, i₆₀: int ::
              (  x₆₁ == i₆₀
                && 1 <= i₆₀
                && i₆₀ < i₂₂
                 ==> (exists i₆₂: int ::
                        i₆₂ < N₂₀
                        && x₆₁ == i₆₂
                        && 1 <= i₆₂
                        && i₆₂ < i₂₂
                        && a₂₁[x₆₁] == 6 + a[0 := 6][-1 + i₆₂])))
        && (forall x₆₃: int ::
                (exists i₆₄: int ::
                        x₆₃ == i₆₄
                        && 1 <= i₆₄
                        && i₆₄ < i₂₂)
                || a₂₁[x₆₃] == a[0 := 6][x₆₃])
        && (forall i₆₅: int ::
              (  i₆₅ <= i₆₅
                && 1 <= i₆₅
                && i₆₅ < i₂₂
                 ==> i₆₅ < N₂₀))
        && i₂₂ < N₂₀
        && x₇ == i₆
        && 1 <= i₆
        && i₆ < i₂₂ + 1
         ==> N₂₀ <= 0
          || (exists i₆₆: int ::
                  i₆₆ < N₂₀
                  && x₇ == i₆₆
                  && 1 <= i₆₆
                  && i₆₆ < i₂₂ + 1
                  && a₂₁[i₂₂ := a₂₁[i₂₂ - 1] + 6][x₇] == 6 + a[0 := 6][-1 + i₆₆])));

goal (forall N₂₀: int, a: [int]int, b: [int]int, a₂₁: [int]int, i₂₂: int, b₂₃: [int]int, i₂₄: int, x₁₁: int, i₁₀: int ::
      (  N₂₀ <= 2147483647 / 4
        && 1 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 1 <= i₆
                && i₆ < i₂₂
                 ==> (exists i₆: int ::
                        i₆ < N₂₀
                        && x₇ == i₆
                        && 1 <= i₆
                        && i₆ < i₂₂
                        && a₂₁[x₇] == 6 + a[0 := 6][-1 + i₆])))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 1 <= i₆
                        && i₆ < i₂₂)
                || a₂₁[x₇] == a[0 := 6][x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 1 <= i₆
                && i₆ < i₂₂
                 ==> i₆ < N₂₀))
        && 1 <= i₂₄
        && i₂₄ <= N₂₀
        && (forall x₁₂₇: int, i₁₂₆: int ::
              (  x₁₂₇ == i₁₂₆
                && 1 <= i₁₂₆
                && i₁₂₆ < i₂₄
                 ==> (exists i₁₂₈: int ::
                        i₁₂₈ < N₂₀
                        && x₁₂₇ == i₁₂₈
                        && 1 <= i₁₂₈
                        && i₁₂₈ < i₂₄
                        && b₂₃[x₁₂₇] == b[0 := 1][-1 + i₁₂₈] + a₂₁[-1 + i₁₂₈])))
        && (forall x₁₂₉: int ::
                (exists i₁₃₀: int ::
                        x₁₂₉ == i₁₃₀
                        && 1 <= i₁₃₀
                        && i₁₃₀ < i₂₄)
                || b₂₃[x₁₂₉] == b[0 := 1][x₁₂₉])
        && (forall i₁₃₁: int ::
              (  i₁₃₁ <= i₁₃₁
                && 1 <= i₁₃₁
                && i₁₃₁ < i₂₄
                 ==> i₁₃₁ < N₂₀))
        && i₂₄ < N₂₀
        && x₁₁ == i₁₀
        && 1 <= i₁₀
        && i₁₀ < i₂₄ + 1
         ==> i₂₂ < N₂₀
          || N₂₀ <= 0
          || (exists i₁₃₂: int ::
                  i₁₃₂ < N₂₀
                  && x₁₁ == i₁₃₂
                  && 1 <= i₁₃₂
                  && i₁₃₂ < i₂₄ + 1
                  && b₂₃[i₂₄ := b₂₃[i₂₄ - 1] + a₂₁[i₂₄ - 1]][x₁₁] == b[0 := 1][-1 + i₁₃₂] + a₂₁[-1 + i₁₃₂])));

goal (forall N₂₀: int, a: [int]int, b: [int]int, c: [int]int, a₂₁: [int]int, i₂₂: int, b₂₃: [int]int, i₂₄: int, c₂₅: [int]int, i₂₆: int, x₁₅: int, i₁₄: int ::
      (  N₂₀ <= 2147483647 / 4
        && 1 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 1 <= i₆
                && i₆ < i₂₂
                 ==> (exists i₆: int ::
                        i₆ < N₂₀
                        && x₇ == i₆
                        && 1 <= i₆
                        && i₆ < i₂₂
                        && a₂₁[x₇] == 6 + a[0 := 6][-1 + i₆])))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 1 <= i₆
                        && i₆ < i₂₂)
                || a₂₁[x₇] == a[0 := 6][x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 1 <= i₆
                && i₆ < i₂₂
                 ==> i₆ < N₂₀))
        && 1 <= i₂₄
        && i₂₄ <= N₂₀
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 1 <= i₁₀
                && i₁₀ < i₂₄
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₀
                        && x₁₁ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₄
                        && b₂₃[x₁₁] == b[0 := 1][-1 + i₁₀] + a₂₁[-1 + i₁₀])))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₄)
                || b₂₃[x₁₁] == b[0 := 1][x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 1 <= i₁₀
                && i₁₀ < i₂₄
                 ==> i₁₀ < N₂₀))
        && 1 <= i₂₆
        && i₂₆ <= N₂₀
        && (forall x₂₂₃: int, i₂₂₂: int ::
              (  x₂₂₃ == i₂₂₂
                && 1 <= i₂₂₂
                && i₂₂₂ < i₂₆
                 ==> (exists i₂₂₄: int ::
                        i₂₂₄ < N₂₀
                        && x₂₂₃ == i₂₂₄
                        && 1 <= i₂₂₄
                        && i₂₂₄ < i₂₆
                        && c₂₅[x₂₂₃] == b₂₃[-1 + i₂₂₄] + c[0 := 0][-1 + i₂₂₄])))
        && (forall x₂₂₅: int ::
                (exists i₂₂₆: int ::
                        x₂₂₅ == i₂₂₆
                        && 1 <= i₂₂₆
                        && i₂₂₆ < i₂₆)
                || c₂₅[x₂₂₅] == c[0 := 0][x₂₂₅])
        && (forall i₂₂₇: int ::
              (  i₂₂₇ <= i₂₂₇
                && 1 <= i₂₂₇
                && i₂₂₇ < i₂₆
                 ==> i₂₂₇ < N₂₀))
        && i₂₆ < N₂₀
        && x₁₅ == i₁₄
        && 1 <= i₁₄
        && i₁₄ < i₂₆ + 1
         ==> i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || (exists i₂₂₈: int ::
                  i₂₂₈ < N₂₀
                  && x₁₅ == i₂₂₈
                  && 1 <= i₂₂₈
                  && i₂₂₈ < i₂₆ + 1
                  && c₂₅[i₂₆ := c₂₅[i₂₆ - 1] + b₂₃[i₂₆ - 1]][x₁₅] == b₂₃[-1 + i₂₂₈] + c[0 := 0][-1 + i₂₂₈])));

goal (forall N₂₀: int, a: [int]int, b: [int]int, c: [int]int, a₂₁: [int]int, i₂₂: int, b₂₃: [int]int, i₂₄: int, c₂₅: [int]int, i₂₆: int, i₂₇: int ::
      (  N₂₀ <= 2147483647 / 4
        && 1 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall x₇: int, i₆: int ::
              (  x₇ == i₆
                && 1 <= i₆
                && i₆ < i₂₂
                 ==> (exists i₆: int ::
                        i₆ < N₂₀
                        && x₇ == i₆
                        && 1 <= i₆
                        && i₆ < i₂₂
                        && a₂₁[x₇] == 6 + a[0 := 6][-1 + i₆])))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == i₆
                        && 1 <= i₆
                        && i₆ < i₂₂)
                || a₂₁[x₇] == a[0 := 6][x₇])
        && (forall i₆: int ::
              (  i₆ <= i₆
                && 1 <= i₆
                && i₆ < i₂₂
                 ==> i₆ < N₂₀))
        && 1 <= i₂₄
        && i₂₄ <= N₂₀
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == i₁₀
                && 1 <= i₁₀
                && i₁₀ < i₂₄
                 ==> (exists i₁₀: int ::
                        i₁₀ < N₂₀
                        && x₁₁ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₄
                        && b₂₃[x₁₁] == b[0 := 1][-1 + i₁₀] + a₂₁[-1 + i₁₀])))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == i₁₀
                        && 1 <= i₁₀
                        && i₁₀ < i₂₄)
                || b₂₃[x₁₁] == b[0 := 1][x₁₁])
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 1 <= i₁₀
                && i₁₀ < i₂₄
                 ==> i₁₀ < N₂₀))
        && 1 <= i₂₆
        && i₂₆ <= N₂₀
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == i₁₄
                && 1 <= i₁₄
                && i₁₄ < i₂₆
                 ==> (exists i₁₄: int ::
                        i₁₄ < N₂₀
                        && x₁₅ == i₁₄
                        && 1 <= i₁₄
                        && i₁₄ < i₂₆
                        && c₂₅[x₁₅] == b₂₃[-1 + i₁₄] + c[0 := 0][-1 + i₁₄])))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == i₁₄
                        && 1 <= i₁₄
                        && i₁₄ < i₂₆)
                || c₂₅[x₁₅] == c[0 := 0][x₁₅])
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 1 <= i₁₄
                && i₁₄ < i₂₆
                 ==> i₁₄ < N₂₀))
        && 0 <= i₂₇
        && i₂₇ <= N₂₀
        && (forall i₁₈: int ::
              (  i₁₈ <= i₁₈
                && 0 <= i₁₈
                && i₁₈ < i₂₇
                 ==> i₁₈ < N₂₀))
        && i₂₇ < N₂₀
         ==> i₂₆ < N₂₀
          || i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || c₂₅[i₂₇] == i₂₇ * i₂₇ * i₂₇));


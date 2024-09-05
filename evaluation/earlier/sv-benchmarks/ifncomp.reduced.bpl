data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₂₀: int, a: [int]int, a₂₁: [int]int, i₂₂: int, x₇: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall x₁₀₃: int, i₆: int ::
              (  x₁₀₃ == 0
                && x₁₀₃ == i₆
                && 0 <= i₆
                && i₆ < i₂₂
                 ==> (exists i₆: int ::
                          i₆ == 0
                          && i₆ < N₂₀
                          && x₁₀₃ == 0
                          && a₂₁[x₁₀₃] == 6)
                  || (exists i₆: int ::
                        (i₆ == 0
                           ==> false))))
        && (forall x₁₀₄: int ::
                (exists i₆: int ::
                        x₁₀₄ == 0
                        && x₁₀₄ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₂)
                || a₂₁[x₁₀₄] == a[x₁₀₄])
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₂
                 ==> i₆ < N₂₀))
        && i₂₂ < N₂₀
         ==> x₇ == 0
          || i₂₂ == 0
          || N₂₀ <= 0
          || a₂₁[i₂₂ := a₂₁[i₂₂ - 1] + 6][x₇] == a[x₇]));

goal (forall N₂₀: int, a: [int]int, b: [int]int, a₂₁: [int]int, i₂₂: int, b₂₃: [int]int, i₂₄: int, x₁₁: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall x₇: int, i₆: int ::
              (  x₇ == 0
                && x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₂
                 ==> (exists i₆: int ::
                          i₆ == 0
                          && i₆ < N₂₀
                          && x₇ == 0
                          && a₂₁[x₇] == 6)
                  || (exists i₆: int ::
                        (i₆ == 0
                           ==> false))))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == 0
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₂)
                || a₂₁[x₇] == a[x₇])
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₂
                 ==> i₆ < N₂₀))
        && 0 <= i₂₄
        && i₂₄ <= N₂₀
        && (forall x₂₂₅: int, i₁₀: int ::
              (  x₂₂₅ == 0
                && x₂₂₅ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₄
                 ==> (exists i₁₀: int ::
                          i₁₀ == 0
                          && i₁₀ < N₂₀
                          && x₂₂₅ == 0
                          && b₂₃[x₂₂₅] == 1)
                  || (exists i₁₀: int ::
                        (i₁₀ == 0
                           ==> false))))
        && (forall x₂₂₆: int ::
                (exists i₁₀: int ::
                        x₂₂₆ == 0
                        && x₂₂₆ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₄)
                || b₂₃[x₂₂₆] == b[x₂₂₆])
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₄
                 ==> i₁₀ < N₂₀))
        && i₂₄ < N₂₀
         ==> x₁₁ == 0
          || i₂₄ == 0
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || b₂₃[i₂₄ := b₂₃[i₂₄ - 1] + a₂₁[i₂₄ - 1]][x₁₁] == b[x₁₁]));

goal (forall N₂₀: int, a: [int]int, b: [int]int, c: [int]int, a₂₁: [int]int, i₂₂: int, b₂₃: [int]int, i₂₄: int, c₂₅: [int]int, i₂₆: int, x₁₅: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall x₇: int, i₆: int ::
              (  x₇ == 0
                && x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₂
                 ==> (exists i₆: int ::
                          i₆ == 0
                          && i₆ < N₂₀
                          && x₇ == 0
                          && a₂₁[x₇] == 6)
                  || (exists i₆: int ::
                        (i₆ == 0
                           ==> false))))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == 0
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₂)
                || a₂₁[x₇] == a[x₇])
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₂
                 ==> i₆ < N₂₀))
        && 0 <= i₂₄
        && i₂₄ <= N₂₀
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == 0
                && x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₄
                 ==> (exists i₁₀: int ::
                          i₁₀ == 0
                          && i₁₀ < N₂₀
                          && x₁₁ == 0
                          && b₂₃[x₁₁] == 1)
                  || (exists i₁₀: int ::
                        (i₁₀ == 0
                           ==> false))))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == 0
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₄)
                || b₂₃[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₄
                 ==> i₁₀ < N₂₀))
        && 0 <= i₂₆
        && i₂₆ <= N₂₀
        && (forall x₄₀₁: int, i₁₄: int ::
              (  x₄₀₁ == 0
                && x₄₀₁ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₆
                 ==> (exists i₁₄: int ::
                          i₁₄ == 0
                          && i₁₄ < N₂₀
                          && x₄₀₁ == 0
                          && c₂₅[x₄₀₁] == N₂₀)
                  || (exists i₁₄: int ::
                        (i₁₄ == 0
                           ==> false))))
        && (forall x₄₀₂: int ::
                (exists i₁₄: int ::
                        x₄₀₂ == 0
                        && x₄₀₂ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₂₆)
                || c₂₅[x₄₀₂] == c[x₄₀₂])
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₂₆
                 ==> i₁₄ < N₂₀))
        && i₂₆ < N₂₀
         ==> x₁₅ == 0
          || i₂₆ == 0
          || i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || c₂₅[i₂₆ := c₂₅[i₂₆ - 1] + b₂₃[i₂₆ - 1]][x₁₅] == c[x₁₅]));

goal (forall N₂₀: int, a: [int]int, b: [int]int, c: [int]int, a₂₁: [int]int, i₂₂: int, b₂₃: [int]int, i₂₄: int, c₂₅: [int]int, i₂₆: int, i₂₇: int ::
      (  N₂₀ <= 2147483647 / 4
        && 0 <= i₂₂
        && i₂₂ <= N₂₀
        && (forall x₇: int, i₆: int ::
              (  x₇ == 0
                && x₇ == i₆
                && 0 <= i₆
                && i₆ < i₂₂
                 ==> (exists i₆: int ::
                          i₆ == 0
                          && i₆ < N₂₀
                          && x₇ == 0
                          && a₂₁[x₇] == 6)
                  || (exists i₆: int ::
                        (i₆ == 0
                           ==> false))))
        && (forall x₇: int ::
                (exists i₆: int ::
                        x₇ == 0
                        && x₇ == i₆
                        && 0 <= i₆
                        && i₆ < i₂₂)
                || a₂₁[x₇] == a[x₇])
        && (forall i₆: int ::
              (  0 <= i₆
                && i₆ < i₂₂
                 ==> i₆ < N₂₀))
        && 0 <= i₂₄
        && i₂₄ <= N₂₀
        && (forall x₁₁: int, i₁₀: int ::
              (  x₁₁ == 0
                && x₁₁ == i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₄
                 ==> (exists i₁₀: int ::
                          i₁₀ == 0
                          && i₁₀ < N₂₀
                          && x₁₁ == 0
                          && b₂₃[x₁₁] == 1)
                  || (exists i₁₀: int ::
                        (i₁₀ == 0
                           ==> false))))
        && (forall x₁₁: int ::
                (exists i₁₀: int ::
                        x₁₁ == 0
                        && x₁₁ == i₁₀
                        && 0 <= i₁₀
                        && i₁₀ < i₂₄)
                || b₂₃[x₁₁] == b[x₁₁])
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₂₄
                 ==> i₁₀ < N₂₀))
        && 0 <= i₂₆
        && i₂₆ <= N₂₀
        && (forall x₁₅: int, i₁₄: int ::
              (  x₁₅ == 0
                && x₁₅ == i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₆
                 ==> (exists i₁₄: int ::
                          i₁₄ == 0
                          && i₁₄ < N₂₀
                          && x₁₅ == 0
                          && c₂₅[x₁₅] == N₂₀)
                  || (exists i₁₄: int ::
                        (i₁₄ == 0
                           ==> false))))
        && (forall x₁₅: int ::
                (exists i₁₄: int ::
                        x₁₅ == 0
                        && x₁₅ == i₁₄
                        && 0 <= i₁₄
                        && i₁₄ < i₂₆)
                || c₂₅[x₁₅] == c[x₁₅])
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₂₆
                 ==> i₁₄ < N₂₀))
        && 0 <= i₂₇
        && i₂₇ <= N₂₀
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₂₇
                 ==> i₁₈ < N₂₀))
        && i₂₇ < N₂₀
         ==> i₂₆ < N₂₀
          || i₂₄ < N₂₀
          || i₂₂ < N₂₀
          || N₂₀ <= 0
          || c₂₅[i₂₇] == N₂₀ + i₂₇ * i₂₇ * i₂₇));


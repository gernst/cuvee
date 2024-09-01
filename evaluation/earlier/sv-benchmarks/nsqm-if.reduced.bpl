data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₅: int, b: [int]int, b₁₆: [int]int, i₁₇: int, x₆: int ::
      (  N₁₅ <= 2147483647 / 4
        && 0 <= i₁₇
        && i₁₇ <= N₁₅
        && (forall x₉₂: int, i₅: int ::
              (  x₉₂ == 0
                && x₉₂ == i₅
                && 0 <= i₅
                && i₅ < i₁₇
                 ==> (exists i₅: int ::
                          i₅ == 0
                          && i₅ < N₁₅
                          && x₉₂ == 0
                          && b₁₆[x₉₂] == 1)
                  || (exists i₅: int ::
                        (i₅ == 0
                           ==> false))))
        && (forall x₉₃: int ::
                (exists i₅: int ::
                        x₉₃ == 0
                        && x₉₃ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₇)
                || b₁₆[x₉₃] == b[x₉₃])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₁₇
                 ==> i₅ < N₁₅))
        && i₁₇ < N₁₅
         ==> x₆ == 0
          || i₁₇ == 0
          || N₁₅ <= 0
          || b₁₆[i₁₇ := b₁₆[i₁₇ - 1] + 2][x₆] == b[x₆]));

goal (forall N₁₅: int, a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, x₁₀: int ::
      (  N₁₅ <= 2147483647 / 4
        && 0 <= i₁₇
        && i₁₇ <= N₁₅
        && (forall x₆: int, i₅: int ::
              (  x₆ == 0
                && x₆ == i₅
                && 0 <= i₅
                && i₅ < i₁₇
                 ==> (exists i₅: int ::
                          i₅ == 0
                          && i₅ < N₁₅
                          && x₆ == 0
                          && b₁₆[x₆] == 1)
                  || (exists i₅: int ::
                        (i₅ == 0
                           ==> false))))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == 0
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₇)
                || b₁₆[x₆] == b[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₁₇
                 ==> i₅ < N₁₅))
        && 0 <= i₁₉
        && i₁₉ <= N₁₅
        && (forall x₂₁₄: int, i₉: int ::
              (  x₂₁₄ == 0
                && x₂₁₄ == i₉
                && 0 <= i₉
                && i₉ < i₁₉
                 ==> (exists i₉: int ::
                          i₉ == 0
                          && i₉ < N₁₅
                          && x₂₁₄ == 0
                          && a₁₈[x₂₁₄] == 1 + N₁₅)
                  || (exists i₉: int ::
                        (i₉ == 0
                           ==> false))))
        && (forall x₂₁₅: int ::
                (exists i₉: int ::
                        x₂₁₅ == 0
                        && x₂₁₅ == i₉
                        && 0 <= i₉
                        && i₉ < i₁₉)
                || a₁₈[x₂₁₅] == a[x₂₁₅])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₁₉
                 ==> i₉ < N₁₅))
        && i₁₉ < N₁₅
         ==> x₁₀ == 0
          || i₁₉ == 0
          || i₁₇ < N₁₅
          || N₁₅ <= 0
          || a₁₈[i₁₉ := a₁₈[i₁₉ - 1] + b₁₆[i₁₉ - 1] + 2][x₁₀] == a[x₁₀]));

goal (forall N₁₅: int, a: [int]int, b: [int]int, b₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, i₂₀: int ::
      (  N₁₅ <= 2147483647 / 4
        && 0 <= i₁₇
        && i₁₇ <= N₁₅
        && (forall x₆: int, i₅: int ::
              (  x₆ == 0
                && x₆ == i₅
                && 0 <= i₅
                && i₅ < i₁₇
                 ==> (exists i₅: int ::
                          i₅ == 0
                          && i₅ < N₁₅
                          && x₆ == 0
                          && b₁₆[x₆] == 1)
                  || (exists i₅: int ::
                        (i₅ == 0
                           ==> false))))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == 0
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₇)
                || b₁₆[x₆] == b[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₁₇
                 ==> i₅ < N₁₅))
        && 0 <= i₁₉
        && i₁₉ <= N₁₅
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == 0
                && x₁₀ == i₉
                && 0 <= i₉
                && i₉ < i₁₉
                 ==> (exists i₉: int ::
                          i₉ == 0
                          && i₉ < N₁₅
                          && x₁₀ == 0
                          && a₁₈[x₁₀] == 1 + N₁₅)
                  || (exists i₉: int ::
                        (i₉ == 0
                           ==> false))))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == 0
                        && x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₁₉)
                || a₁₈[x₁₀] == a[x₁₀])
        && (forall i₉: int ::
              (  i₉ <= i₉
                && 0 <= i₉
                && i₉ < i₁₉
                 ==> i₉ < N₁₅))
        && 0 <= i₂₀
        && i₂₀ <= N₁₅
        && (forall i₁₃: int ::
              (  i₁₃ <= i₁₃
                && 0 <= i₁₃
                && i₁₃ < i₂₀
                 ==> i₁₃ < N₁₅))
        && i₂₀ < N₁₅
         ==> i₁₉ < N₁₅
          || i₁₇ < N₁₅
          || N₁₅ <= 0
          || a₁₈[i₂₀] == N₁₅ + (i₂₀ + 1) * (i₂₀ + 1)));


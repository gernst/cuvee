data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₄: int, a: [int]int, a₁₅: [int]int, i₁₆: int, a₁₇: [int]int, i₁₈: int, i₈: int ::
      (  N₁₄ <= 2147483647 / 4
        && 0 <= i₁₆
        && i₁₆ <= N₁₄
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₆
                 ==> i₅ < N₁₄
                  && a₁₅[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₆
                || a₁₅[i₅] == a[i₅])
        && 0 <= i₁₈
        && i₁₈ <= N₁₄
        && (forall i₁₆₆: int ::
              (  0 <= i₁₆₆
                && i₁₆₆ < i₁₈
                 ==> a₁₇[i₁₆₆] == 1
                    && i₁₆₆ < N₁₄
                    && a₁₇[i₁₆₆] == 3 + a₁₅[i₁₆₆]
                  ||   (a₁₇[i₁₆₆] == 1
                       ==> false)
                    && i₁₆₆ < N₁₄
                    && a₁₇[i₁₆₆] == -1 + a₁₅[i₁₆₆]))
        && (forall i₁₆₇: int ::
                  0 <= i₁₆₇
                  && i₁₆₇ < i₁₈
                || a₁₇[i₁₆₇] == a₁₅[i₁₆₇])
        && i₁₈ < N₁₄
        && a₁₇[i₁₈] == 1
        && 0 <= i₈
        && i₈ < i₁₈ + 1
         ==> i₁₆ < N₁₄
          || N₁₄ <= 0
          || a₁₇[i₁₈ := a₁₇[i₁₈] + 3][i₈] == 1
          || a₁₇[i₁₈ := a₁₇[i₁₈] + 3][i₈] == -1 + a₁₅[i₈]));

goal (forall N₁₄: int, sum: [int]int, a: [int]int, a₁₅: [int]int, i₁₆: int, a₁₇: [int]int, i₁₈: int, sum₁₉: [int]int, i₂₀: int ::
      (  N₁₄ <= 2147483647 / 4
        && 0 <= i₁₆
        && i₁₆ <= N₁₄
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₆
                 ==> i₅ < N₁₄
                  && a₁₅[i₅] == 1))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₆
                || a₁₅[i₅] == a[i₅])
        && 0 <= i₁₈
        && i₁₈ <= N₁₄
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₈
                 ==> a₁₇[i₈] == 1
                    && i₈ < N₁₄
                    && a₁₇[i₈] == 3 + a₁₅[i₈]
                  ||   (a₁₇[i₈] == 1
                       ==> false)
                    && i₈ < N₁₄
                    && a₁₇[i₈] == -1 + a₁₅[i₈]))
        && (forall i₈: int ::
                  0 <= i₈
                  && i₈ < i₁₈
                || a₁₇[i₈] == a₁₅[i₈])
        && 0 <= i₂₀
        && i₂₀ <= N₁₄
        && (forall i₁₁: int ::
              (  0 <= i₁₁
                && i₁₁ < i₂₀
                 ==> i₁₁ < N₁₄
                  && sum₁₉[0] == sum[0 := 0][0] + a₁₇[i₁₁]))
        && (forall i₁₁: int ::
                  0 <= i₁₁
                  && i₁₁ < i₂₀
                || sum₁₉[0] == sum[0 := 0][0])
         ==> i₂₀ < N₁₄
          || i₁₈ < N₁₄
          || i₁₆ < N₁₄
          || N₁₄ <= 0
          || sum₁₉[0] == 4 * N₁₄));


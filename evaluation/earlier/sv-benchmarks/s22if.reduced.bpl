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
        && (forall i₁₆₈: int ::
              (  0 <= i₁₆₈
                && i₁₆₈ < i₁₈
                 ==> a₁₇[i₁₆₈] == 1
                    && i₁₆₈ < N₁₄
                    && a₁₇[i₁₆₈] == 2 + a₁₅[i₁₆₈]
                  ||   (a₁₇[i₁₆₈] == 1
                       ==> false)
                    && i₁₆₈ < N₁₄
                    && a₁₇[i₁₆₈] == -1 + a₁₅[i₁₆₈]))
        && (forall i₁₆₉: int ::
                  0 <= i₁₆₉
                  && i₁₆₉ < i₁₈
                || a₁₇[i₁₆₉] == a₁₅[i₁₆₉])
        && i₁₈ < N₁₄
        && a₁₇[i₁₈] == 1
        && 0 <= i₈
        && i₈ < i₁₈ + 1
         ==> i₁₆ < N₁₄
          || N₁₄ <= 0
          || a₁₇[i₁₈ := a₁₇[i₁₈] + 2][i₈] == 1
          || a₁₇[i₁₈ := a₁₇[i₁₈] + 2][i₈] == -1 + a₁₅[i₈]));

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
                    && a₁₇[i₈] == 2 + a₁₅[i₈]
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
                 ==> a₁₇[i₁₁] == 3
                    && i₁₁ < N₁₄
                    && sum₁₉[0] == sum[0 := 0][0] + a₁₇[i₁₁]
                  ||   (a₁₇[i₁₁] == 3
                       ==> false)
                    && i₁₁ < N₁₄
                    && sum₁₉[0] == sum[0 := 0][0] * a₁₇[i₁₁]))
        && (forall i₁₁: int ::
                  0 <= i₁₁
                  && i₁₁ < i₂₀
                || sum₁₉[0] == sum[0 := 0][0])
         ==> i₂₀ < N₁₄
          || i₁₈ < N₁₄
          || i₁₆ < N₁₄
          || N₁₄ <= 0
          || sum₁₉[0] == 3 * N₁₄));


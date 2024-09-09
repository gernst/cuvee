data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₄: int, a: [int]int, a₁₅: [int]int, i₁₆: int, a₁₇: [int]int, i₁₈: int, i₈: int ::
      (  N₁₄ <= 2147483647 / 4
        && 0 <= i₁₆
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
        && (forall i₁₅₁: int ::
              (  0 <= i₁₅₁
                && i₁₅₁ < i₁₈
                 ==> a₁₇[i₁₅₁] == 1
                    && i₁₅₁ < N₁₄
                    && a₁₇[i₁₅₁] == 2 + a₁₅[i₁₅₁]
                  ||   (a₁₇[i₁₅₁] == 1
                       ==> false)
                    && i₁₅₁ < N₁₄
                    && a₁₇[i₁₅₁] == -1 + a₁₅[i₁₅₁]))
        && (forall i₁₅₂: int ::
                  0 <= i₁₅₂
                  && i₁₅₂ < i₁₈
                || a₁₇[i₁₅₂] == a₁₅[i₁₅₂])
        && i₁₈ < N₁₄
        && a₁₇[i₁₈] == 1
        && 0 <= i₈
        && i₈ < i₁₈ + 1
         ==> i₁₆ < N₁₄
          || N₁₄ <= 0
          || a₁₇[i₁₈ := a₁₇[i₁₈] + 2][i₈] == 1
          || a₁₇[i₁₈ := a₁₇[i₁₈] + 2][i₈] == -1 + a₁₅[i₈]));


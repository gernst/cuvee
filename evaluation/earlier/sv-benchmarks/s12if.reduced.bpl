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
        && (forall i₁₅₃: int ::
              (  0 <= i₁₅₃
                && i₁₅₃ < i₁₈
                 ==> a₁₇[i₁₅₃] == 1
                    && i₁₅₃ < N₁₄
                    && a₁₇[i₁₅₃] == 1 + a₁₅[i₁₅₃]
                  ||   (a₁₇[i₁₅₃] == 1
                       ==> false)
                    && i₁₅₃ < N₁₄
                    && a₁₇[i₁₅₃] == -1 + a₁₅[i₁₅₃]))
        && (forall i₁₅₄: int ::
                  0 <= i₁₅₄
                  && i₁₅₄ < i₁₈
                || a₁₇[i₁₅₄] == a₁₅[i₁₅₄])
        && i₁₈ < N₁₄
        && a₁₇[i₁₈] == 1
        && 0 <= i₈
        && i₈ < i₁₈ + 1
         ==> i₁₆ < N₁₄
          || N₁₄ <= 0
          || a₁₇[i₁₈ := a₁₇[i₁₈] + 1][i₈] == 1
          || a₁₇[i₁₈ := a₁₇[i₁₈] + 1][i₈] == -1 + a₁₅[i₈]));


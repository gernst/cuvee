data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₄: int, a: [int]int, a₁₅: [int]int, i₁₆: int, a₁₇: [int]int, i₁₈: int, i₁₉: int ::
      (  N₁₄ <= 2147483647 / 4
        && 0 <= i₁₆
        && i₁₆ <= N₁₄
        && (forall x₅: int, i₄: int ::
              (  x₅ == i₄
                && 0 <= i₄
                && i₄ < i₁₆
                 ==> (exists i₄: int ::
                        i₄ < N₁₄
                        && x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₆
                        && a₁₅[x₅] == 0)))
        && (forall x₅: int ::
                (exists i₄: int ::
                        x₅ == i₄
                        && 0 <= i₄
                        && i₄ < i₁₆)
                || a₁₅[x₅] == a[x₅])
        && (forall i₄: int ::
              (  0 <= i₄
                && i₄ < i₁₆
                 ==> i₄ < N₁₄))
        && 0 <= i₁₈
        && i₁₈ <= N₁₄
        && (forall x₉: int, i₈: int ::
              (  x₉ == i₈
                && 0 <= i₈
                && i₈ < i₁₈
                && N₁₄ % 2 == 0
                 ==> (exists i₈: int ::
                        N₁₄ % 2 == 0
                        && i₈ < N₁₄
                        && x₉ == i₈
                        && 0 <= i₈
                        && i₈ < i₁₈
                        && a₁₇[x₉] == 2 + a₁₅[i₈])))
        && (forall x₉: int ::
                (exists i₈: int ::
                        x₉ == i₈
                        && 0 <= i₈
                        && i₈ < i₁₈)
                || a₁₇[x₉] == a₁₅[x₉])
        && (forall i₈: int ::
              (  0 <= i₈
                && i₈ < i₁₈
                 ==> i₈ < N₁₄))
        && 0 <= i₁₉
        && i₁₉ <= N₁₄
        && (forall i₁₂: int ::
              (  0 <= i₁₂
                && i₁₂ < i₁₉
                 ==> i₁₂ < N₁₄))
        && i₁₉ < N₁₄
         ==> i₁₈ < N₁₄
          || i₁₆ < N₁₄
          || N₁₄ <= 0
          || a₁₇[i₁₉] % 2 == N₁₄ % 2));


data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₅: int, a: [int]int, a₁₆: [int]int, i₁₇: int, a₁₈: [int]int, i₁₉: int, i₂₀: int ::
      (  N₁₅ <= 2147483647 / 4
        && 0 <= i₁₇
        && i₁₇ <= N₁₅
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₁₇
                 ==> (exists __VERIFIER_nondet_int₁₄: int, i₅: int ::
                        i₅ < N₁₅
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₇
                        && a₁₆[x₆] == __VERIFIER_nondet_int₁₄)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₁₇)
                || a₁₆[x₆] == a[x₆])
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₇
                 ==> i₅ < N₁₅))
        && 0 <= i₁₉
        && i₁₉ <= N₁₅
        && (forall x₁₀: int, i₉: int ::
              (  x₁₀ == i₉
                && 0 <= i₉
                && i₉ < i₁₉
                 ==> (exists i₉: int ::
                          a₁₈[i₉] < N₁₅
                          && i₉ < N₁₅
                          && x₁₀ == i₉
                          && 0 <= i₉
                          && i₉ < i₁₉
                          && a₁₈[x₁₀] == a₁₆[i₉])
                  || (exists i₉: int ::
                        (a₁₈[i₉] < N₁₅
                           ==> false))))
        && (forall x₁₀: int ::
                (exists i₉: int ::
                        x₁₀ == i₉
                        && 0 <= i₉
                        && i₉ < i₁₉)
                || a₁₈[x₁₀] == a₁₆[x₁₀])
        && (forall i₉: int ::
              (  0 <= i₉
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
          || a₁₈[i₂₀] <= N₁₅));


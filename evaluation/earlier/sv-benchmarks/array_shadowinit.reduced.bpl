data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₂: int, a: [int]int, a₁₃: [int]int, i₁₄: int, k₁₅: int, i₅: int, k₆: int ::
      (  0 < N₁₂
        && 0 <= i₁₄
        && 0 <= k₁₅
        && (forall i₆₈: int, k₆₇: int ::
              (  0 <= i₆₈
                && i₆₈ < i₁₄
                && 0 <= k₆₇
                && k₆₇ < k₁₅
                 ==> i₆₈ < N₁₂
                  && a₁₃[k₆₇] == k₆₇))
        && (forall i₇₀: int, k₆₉: int ::
                  0 <= i₇₀
                  && i₇₀ < i₁₄
                  && 0 <= k₆₉
                  && k₆₉ < k₁₅
                || a₁₃[k₆₉] == a[k₆₉])
        && i₁₄ < N₁₂
        && 0 <= i₅
        && i₅ < i₁₄ + 1
        && 0 <= k₆
        && k₆ < k₁₅ + 1
         ==> a₁₃[k₁₅ := k₁₅][k₆] == k₆));

goal (forall N₁₂: int, a: [int]int, a₁₃: [int]int, i₁₄: int, k₁₅: int, i₅: int, k₆: int ::
      (  0 < N₁₂
        && 0 <= i₁₄
        && 0 <= k₁₅
        && (forall i₇₉: int, k₇₈: int ::
              (  0 <= i₇₉
                && i₇₉ < i₁₄
                && 0 <= k₇₈
                && k₇₈ < k₁₅
                 ==> i₇₉ < N₁₂
                  && a₁₃[k₇₈] == k₇₈))
        && (forall i₈₁: int, k₈₀: int ::
                  0 <= i₈₁
                  && i₈₁ < i₁₄
                  && 0 <= k₈₀
                  && k₈₀ < k₁₅
                || a₁₃[k₈₀] == a[k₈₀])
        && i₁₄ < N₁₂
         ==> 0 <= i₅
          || a₁₃[k₁₅ := k₁₅][k₆] == a[k₆]));

goal (forall N₁₂: int, a: [int]int, a₁₃: [int]int, i₁₄: int, k₁₅: int, i₅: int, k₆: int ::
      (  0 < N₁₂
        && 0 <= i₁₄
        && 0 <= k₁₅
        && (forall i₉₀: int, k₈₉: int ::
              (  0 <= i₉₀
                && i₉₀ < i₁₄
                && 0 <= k₈₉
                && k₈₉ < k₁₅
                 ==> i₉₀ < N₁₂
                  && a₁₃[k₈₉] == k₈₉))
        && (forall i₉₂: int, k₉₁: int ::
                  0 <= i₉₂
                  && i₉₂ < i₁₄
                  && 0 <= k₉₁
                  && k₉₁ < k₁₅
                || a₁₃[k₉₁] == a[k₉₁])
        && i₁₄ < N₁₂
         ==> i₅ < i₁₄ + 1
          || a₁₃[k₁₅ := k₁₅][k₆] == a[k₆]));

goal (forall N₁₂: int, a: [int]int, a₁₃: [int]int, i₁₄: int, k₁₅: int, i₁₆: int ::
      (  0 < N₁₂
        && 0 <= i₁₄
        && 0 <= k₁₅
        && (forall i₅: int, k₆: int ::
              (  0 <= i₅
                && i₅ < i₁₄
                && 0 <= k₆
                && k₆ < k₁₅
                 ==> i₅ < N₁₂
                  && a₁₃[k₆] == k₆))
        && (forall i₅: int, k₆: int ::
                  0 <= i₅
                  && i₅ < i₁₄
                  && 0 <= k₆
                  && k₆ < k₁₅
                || a₁₃[k₆] == a[k₆])
        && 0 <= i₁₆
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₁₆
                 ==> i₁₀ < N₁₂))
        && i₁₆ < N₁₂
         ==> i₁₄ < N₁₂
          || a₁₃[i₁₆] == i₁₆));


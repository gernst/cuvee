data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall N₁₂: int, a: [int]int, a₁₃: [int]int, i₁₄: int, k₁₅: int, i₅: int, k₆: int ::
      (  0 < N₁₂
        && 0 <= i₁₄
        && 0 <= k₁₅
        && i₁₄ <= N₁₂
        && (forall i₇₄: int, k₇₃: int ::
              (  0 <= i₇₄
                && i₇₄ < i₁₄
                && 0 <= k₇₃
                && k₇₃ < k₁₅
                 ==> i₇₄ < N₁₂
                  && a₁₃[k₇₃] == k₇₃))
        && (forall i₇₆: int, k₇₅: int ::
                  0 <= i₇₆
                  && i₇₆ < i₁₄
                  && 0 <= k₇₅
                  && k₇₅ < k₁₅
                || a₁₃[k₇₅] == a[k₇₅])
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
        && i₁₄ <= N₁₂
        && (forall i₈₅: int, k₈₄: int ::
              (  0 <= i₈₅
                && i₈₅ < i₁₄
                && 0 <= k₈₄
                && k₈₄ < k₁₅
                 ==> i₈₅ < N₁₂
                  && a₁₃[k₈₄] == k₈₄))
        && (forall i₈₇: int, k₈₆: int ::
                  0 <= i₈₇
                  && i₈₇ < i₁₄
                  && 0 <= k₈₆
                  && k₈₆ < k₁₅
                || a₁₃[k₈₆] == a[k₈₆])
        && i₁₄ < N₁₂
         ==> 0 <= i₅
          || a₁₃[k₁₅ := k₁₅][k₆] == a[k₆]));

goal (forall N₁₂: int, a: [int]int, a₁₃: [int]int, i₁₄: int, k₁₅: int, i₅: int, k₆: int ::
      (  0 < N₁₂
        && 0 <= i₁₄
        && 0 <= k₁₅
        && i₁₄ <= N₁₂
        && (forall i₉₆: int, k₉₅: int ::
              (  0 <= i₉₆
                && i₉₆ < i₁₄
                && 0 <= k₉₅
                && k₉₅ < k₁₅
                 ==> i₉₆ < N₁₂
                  && a₁₃[k₉₅] == k₉₅))
        && (forall i₉₈: int, k₉₇: int ::
                  0 <= i₉₈
                  && i₉₈ < i₁₄
                  && 0 <= k₉₇
                  && k₉₇ < k₁₅
                || a₁₃[k₉₇] == a[k₉₇])
        && i₁₄ < N₁₂
         ==> i₅ < i₁₄ + 1
          || a₁₃[k₁₅ := k₁₅][k₆] == a[k₆]));

goal (forall N₁₂: int, a: [int]int, a₁₃: [int]int, i₁₄: int, k₁₅: int, i₁₆: int ::
      (  0 < N₁₂
        && 0 <= i₁₄
        && 0 <= k₁₅
        && i₁₄ <= N₁₂
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
        && i₁₆ <= N₁₂
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₁₆
                 ==> i₁₀ < N₁₂))
        && i₁₆ < N₁₂
         ==> i₁₄ < N₁₂
          || a₁₃[i₁₆] == i₁₆));


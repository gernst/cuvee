data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall SIZE₄₉: int, a: [int]int, a₅₁: [int]int, i₅₂: int, i₅₄: int, i₅₆: int, i₅₈: int, i₆₀: int, i₆₂: int, i₆₄: int, i₆₆: int, i₆₈: int, i₇₀: int, sum₇₁: int, i₇₂: int ::
      (  1 < SIZE₄₉
        && 0 <= i₅₂
        && i₅₂ <= SIZE₄₉
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₅₂
                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                        i₅ < SIZE₄₉
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₅₂
                        && a₅₁[x₆] == __VERIFIER_nondet_short₁₄)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₅₂)
                || a₅₁[x₆] == a[x₆])
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₅₂
                 ==> i₅ < SIZE₄₉))
        && 0 <= i₅₄
        && i₅₄ <= SIZE₄₉
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₅₄
                 ==> i₁₀ < SIZE₄₉))
        && 0 <= i₅₆
        && i₅₆ <= SIZE₄₉
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₅₆
                 ==> i₁₄ < SIZE₄₉))
        && 0 <= i₅₈
        && i₅₈ <= SIZE₄₉
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₅₈
                 ==> i₁₈ < SIZE₄₉))
        && 0 <= i₆₀
        && i₆₀ <= SIZE₄₉
        && (forall i₂₂: int ::
              (  0 <= i₂₂
                && i₂₂ < i₆₀
                 ==> i₂₂ < SIZE₄₉))
        && 0 <= i₆₂
        && i₆₂ <= SIZE₄₉
        && (forall i₂₆: int ::
              (  0 <= i₂₆
                && i₂₆ < i₆₂
                 ==> i₂₆ < SIZE₄₉))
        && 0 <= i₆₄
        && i₆₄ <= SIZE₄₉
        && (forall i₃₀: int ::
              (  0 <= i₃₀
                && i₃₀ < i₆₄
                 ==> i₃₀ < SIZE₄₉))
        && 0 <= i₆₆
        && i₆₆ <= SIZE₄₉
        && (forall i₃₄: int ::
              (  0 <= i₃₄
                && i₃₄ < i₆₆
                 ==> i₃₄ < SIZE₄₉))
        && 0 <= i₆₈
        && i₆₈ <= SIZE₄₉
        && (forall i₃₈: int ::
              (  0 <= i₃₈
                && i₃₈ < i₆₈
                 ==> i₃₈ < SIZE₄₉))
        && 0 <= i₇₀
        && i₇₀ <= SIZE₄₉
        && (forall i₄₂: int ::
              (  0 <= i₄₂
                && i₄₂ < i₇₀
                 ==> i₄₂ < SIZE₄₉))
        && 0 <= i₇₂
        && i₇₂ <= SIZE₄₉
        && (forall i₄₆: int ::
              (  0 <= i₄₆
                && i₄₆ < i₇₂
                 ==> i₄₆ < SIZE₄₉))
         ==> i₇₂ < SIZE₄₉
          || i₇₀ < SIZE₄₉
          || i₆₈ < SIZE₄₉
          || i₆₆ < SIZE₄₉
          || i₆₄ < SIZE₄₉
          || i₆₂ < SIZE₄₉
          || i₆₀ < SIZE₄₉
          || i₅₈ < SIZE₄₉
          || i₅₆ < SIZE₄₉
          || i₅₄ < SIZE₄₉
          || i₅₂ < SIZE₄₉
          || sum₇₁ == 0));


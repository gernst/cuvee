data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall SIZE₄₁: int, a: [int]int, a₄₃: [int]int, i₄₄: int, i₄₆: int, i₄₈: int, i₅₀: int, i₅₂: int, i₅₄: int, i₅₆: int, i₅₈: int, sum₅₉: int, i₆₀: int ::
      (  1 < SIZE₄₁
        && 0 <= i₄₄
        && i₄₄ <= SIZE₄₁
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₄₄
                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                        i₅ < SIZE₄₁
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₄₄
                        && a₄₃[x₆] == __VERIFIER_nondet_short₁₄)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₄₄)
                || a₄₃[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₄₄
                 ==> i₅ < SIZE₄₁))
        && 0 <= i₄₆
        && i₄₆ <= SIZE₄₁
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₄₆
                 ==> i₁₀ < SIZE₄₁))
        && 0 <= i₄₈
        && i₄₈ <= SIZE₄₁
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₄₈
                 ==> i₁₄ < SIZE₄₁))
        && 0 <= i₅₀
        && i₅₀ <= SIZE₄₁
        && (forall i₁₈: int ::
              (  i₁₈ <= i₁₈
                && 0 <= i₁₈
                && i₁₈ < i₅₀
                 ==> i₁₈ < SIZE₄₁))
        && 0 <= i₅₂
        && i₅₂ <= SIZE₄₁
        && (forall i₂₂: int ::
              (  i₂₂ <= i₂₂
                && 0 <= i₂₂
                && i₂₂ < i₅₂
                 ==> i₂₂ < SIZE₄₁))
        && 0 <= i₅₄
        && i₅₄ <= SIZE₄₁
        && (forall i₂₆: int ::
              (  i₂₆ <= i₂₆
                && 0 <= i₂₆
                && i₂₆ < i₅₄
                 ==> i₂₆ < SIZE₄₁))
        && 0 <= i₅₆
        && i₅₆ <= SIZE₄₁
        && (forall i₃₀: int ::
              (  i₃₀ <= i₃₀
                && 0 <= i₃₀
                && i₃₀ < i₅₆
                 ==> i₃₀ < SIZE₄₁))
        && 0 <= i₅₈
        && i₅₈ <= SIZE₄₁
        && (forall i₃₄: int ::
              (  i₃₄ <= i₃₄
                && 0 <= i₃₄
                && i₃₄ < i₅₈
                 ==> i₃₄ < SIZE₄₁))
        && 0 <= i₆₀
        && i₆₀ <= SIZE₄₁
        && (forall i₃₈: int ::
              (  i₃₈ <= i₃₈
                && 0 <= i₃₈
                && i₃₈ < i₆₀
                 ==> i₃₈ < SIZE₄₁))
         ==> i₆₀ < SIZE₄₁
          || i₅₈ < SIZE₄₁
          || i₅₆ < SIZE₄₁
          || i₅₄ < SIZE₄₁
          || i₅₂ < SIZE₄₁
          || i₅₀ < SIZE₄₁
          || i₄₈ < SIZE₄₁
          || i₄₆ < SIZE₄₁
          || i₄₄ < SIZE₄₁
          || sum₅₉ == 0));


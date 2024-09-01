data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall SIZE₂₅: int, a: [int]int, a₂₇: [int]int, i₂₈: int, i₃₀: int, i₃₂: int, i₃₄: int, sum₃₅: int, i₃₆: int ::
      (  1 < SIZE₂₅
        && 0 <= i₂₈
        && i₂₈ <= SIZE₂₅
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₈
                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                        i₅ < SIZE₂₅
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₈
                        && a₂₇[x₆] == __VERIFIER_nondet_short₁₄)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₈)
                || a₂₇[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₂₈
                 ==> i₅ < SIZE₂₅))
        && 0 <= i₃₀
        && i₃₀ <= SIZE₂₅
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₃₀
                 ==> i₁₀ < SIZE₂₅))
        && 0 <= i₃₂
        && i₃₂ <= SIZE₂₅
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₃₂
                 ==> i₁₄ < SIZE₂₅))
        && 0 <= i₃₄
        && i₃₄ <= SIZE₂₅
        && (forall i₁₈: int ::
              (  i₁₈ <= i₁₈
                && 0 <= i₁₈
                && i₁₈ < i₃₄
                 ==> i₁₈ < SIZE₂₅))
        && 0 <= i₃₆
        && i₃₆ <= SIZE₂₅
        && (forall i₂₂: int ::
              (  i₂₂ <= i₂₂
                && 0 <= i₂₂
                && i₂₂ < i₃₆
                 ==> i₂₂ < SIZE₂₅))
         ==> i₃₆ < SIZE₂₅
          || i₃₄ < SIZE₂₅
          || i₃₂ < SIZE₂₅
          || i₃₀ < SIZE₂₅
          || i₂₈ < SIZE₂₅
          || sum₃₅ == 0));


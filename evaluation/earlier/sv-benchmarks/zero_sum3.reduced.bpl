data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall SIZE₃₃: int, a: [int]int, a₃₅: [int]int, i₃₆: int, i₃₈: int, i₄₀: int, i₄₂: int, i₄₄: int, i₄₆: int, sum₄₇: int, i₄₈: int ::
      (  1 < SIZE₃₃
        && 0 <= i₃₆
        && i₃₆ <= SIZE₃₃
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₃₆
                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                        i₅ < SIZE₃₃
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₃₆
                        && a₃₅[x₆] == __VERIFIER_nondet_short₁₄)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₃₆)
                || a₃₅[x₆] == a[x₆])
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₆
                 ==> i₅ < SIZE₃₃))
        && 0 <= i₃₈
        && i₃₈ <= SIZE₃₃
        && (forall i₁₀: int ::
              (  0 <= i₁₀
                && i₁₀ < i₃₈
                 ==> i₁₀ < SIZE₃₃))
        && 0 <= i₄₀
        && i₄₀ <= SIZE₃₃
        && (forall i₁₄: int ::
              (  0 <= i₁₄
                && i₁₄ < i₄₀
                 ==> i₁₄ < SIZE₃₃))
        && 0 <= i₄₂
        && i₄₂ <= SIZE₃₃
        && (forall i₁₈: int ::
              (  0 <= i₁₈
                && i₁₈ < i₄₂
                 ==> i₁₈ < SIZE₃₃))
        && 0 <= i₄₄
        && i₄₄ <= SIZE₃₃
        && (forall i₂₂: int ::
              (  0 <= i₂₂
                && i₂₂ < i₄₄
                 ==> i₂₂ < SIZE₃₃))
        && 0 <= i₄₆
        && i₄₆ <= SIZE₃₃
        && (forall i₂₆: int ::
              (  0 <= i₂₆
                && i₂₆ < i₄₆
                 ==> i₂₆ < SIZE₃₃))
        && 0 <= i₄₈
        && i₄₈ <= SIZE₃₃
        && (forall i₃₀: int ::
              (  0 <= i₃₀
                && i₃₀ < i₄₈
                 ==> i₃₀ < SIZE₃₃))
         ==> i₄₈ < SIZE₃₃
          || i₄₆ < SIZE₃₃
          || i₄₄ < SIZE₃₃
          || i₄₂ < SIZE₃₃
          || i₄₀ < SIZE₃₃
          || i₃₈ < SIZE₃₃
          || i₃₆ < SIZE₃₃
          || sum₄₇ == 0));


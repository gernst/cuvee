data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall SIZE₁₇: int, a: [int]int, a₁₉: [int]int, i₂₀: int, i₂₂: int, sum₂₃: int, i₂₄: int ::
      (  1 < SIZE₁₇
        && 0 <= i₂₀
        && i₂₀ <= SIZE₁₇
        && (forall x₆: int, i₅: int ::
              (  x₆ == i₅
                && 0 <= i₅
                && i₅ < i₂₀
                 ==> (exists __VERIFIER_nondet_short₁₄: int, i₅: int ::
                        i₅ < SIZE₁₇
                        && x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₀
                        && a₁₉[x₆] == __VERIFIER_nondet_short₁₄)))
        && (forall x₆: int ::
                (exists i₅: int ::
                        x₆ == i₅
                        && 0 <= i₅
                        && i₅ < i₂₀)
                || a₁₉[x₆] == a[x₆])
        && (forall i₅: int ::
              (  i₅ <= i₅
                && 0 <= i₅
                && i₅ < i₂₀
                 ==> i₅ < SIZE₁₇))
        && 0 <= i₂₂
        && i₂₂ <= SIZE₁₇
        && (forall i₁₀: int ::
              (  i₁₀ <= i₁₀
                && 0 <= i₁₀
                && i₁₀ < i₂₂
                 ==> i₁₀ < SIZE₁₇))
        && 0 <= i₂₄
        && i₂₄ <= SIZE₁₇
        && (forall i₁₄: int ::
              (  i₁₄ <= i₁₄
                && 0 <= i₁₄
                && i₁₄ < i₂₄
                 ==> i₁₄ < SIZE₁₇))
         ==> i₂₄ < SIZE₁₇
          || i₂₂ < SIZE₁₇
          || i₂₀ < SIZE₁₇
          || sum₂₃ == 0));


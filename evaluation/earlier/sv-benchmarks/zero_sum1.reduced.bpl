data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal (forall SIZE₁₆: int, a: [int]int, a₁₈: [int]int, i₁₉: int, i₂₁: int, sum₂₂: int, i₂₃: int ::
      (  1 < SIZE₁₆
        && 0 <= i₁₉
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₁₉
                 ==> (exists __VERIFIER_nondet_short₁₄: int ::
                        i₅ < SIZE₁₆
                        && a₁₈[i₅] == __VERIFIER_nondet_short₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₁₉
                || a₁₈[i₅] == a[i₅])
        && 0 <= i₂₁
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₁
                 ==> i₉ < SIZE₁₆))
        && 0 <= i₂₃
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₂₃
                 ==> i₁₃ < SIZE₁₆))
         ==> i₂₃ < SIZE₁₆
          || i₂₁ < SIZE₁₆
          || i₁₉ < SIZE₁₆
          || sum₂₂ == 0));


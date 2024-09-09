data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall SIZE₃₂: int, a: [int]int, a₃₄: [int]int, i₃₅: int, i₃₇: int, i₃₉: int, i₄₁: int, i₄₃: int, i₄₅: int, sum₄₆: int, i₄₇: int ::
      (  1 < SIZE₃₂
        && 0 <= i₃₅
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₃₅
                 ==> (exists __VERIFIER_nondet_short₁₄: int ::
                        i₅ < SIZE₃₂
                        && a₃₄[i₅] == __VERIFIER_nondet_short₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₃₅
                || a₃₄[i₅] == a[i₅])
        && 0 <= i₃₇
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₃₇
                 ==> i₉ < SIZE₃₂))
        && 0 <= i₃₉
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₃₉
                 ==> i₁₃ < SIZE₃₂))
        && 0 <= i₄₁
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₄₁
                 ==> i₁₇ < SIZE₃₂))
        && 0 <= i₄₃
        && (forall i₂₁: int ::
              (  0 <= i₂₁
                && i₂₁ < i₄₃
                 ==> i₂₁ < SIZE₃₂))
        && 0 <= i₄₅
        && (forall i₂₅: int ::
              (  0 <= i₂₅
                && i₂₅ < i₄₅
                 ==> i₂₅ < SIZE₃₂))
        && 0 <= i₄₇
        && (forall i₂₉: int ::
              (  0 <= i₂₉
                && i₂₉ < i₄₇
                 ==> i₂₉ < SIZE₃₂))
         ==> i₄₇ < SIZE₃₂
          || i₄₅ < SIZE₃₂
          || i₄₃ < SIZE₃₂
          || i₄₁ < SIZE₃₂
          || i₃₉ < SIZE₃₂
          || i₃₇ < SIZE₃₂
          || i₃₅ < SIZE₃₂
          || sum₄₆ == 0));


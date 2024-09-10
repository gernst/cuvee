data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall SIZE₂₄: int, a: [int]int, a₂₆: [int]int, i₂₇: int, i₂₉: int, i₃₁: int, i₃₃: int, sum₃₄: int, i₃₅: int ::
      (  -32768 <= SIZE₂₄
        && SIZE₂₄ < 32768
        && 1 < SIZE₂₄
        && 0 <= i₂₇
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₂₇
                 ==> (exists nondet_short₁₄: int ::
                        -32768 <= nondet_short₁₄
                        && nondet_short₁₄ < 32768
                        && i₅ < SIZE₂₄
                        && a₂₆[i₅] == nondet_short₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₂₇
                || a₂₆[i₅] == a[i₅])
        && 0 <= i₂₉
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₂₉
                 ==> i₉ < SIZE₂₄))
        && 0 <= i₃₁
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₃₁
                 ==> i₁₃ < SIZE₂₄))
        && 0 <= i₃₃
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₃₃
                 ==> i₁₇ < SIZE₂₄))
        && 0 <= i₃₅
        && (forall i₂₁: int ::
              (  0 <= i₂₁
                && i₂₁ < i₃₅
                 ==> i₂₁ < SIZE₂₄))
         ==> i₃₅ < SIZE₂₄
          || i₃₃ < SIZE₂₄
          || i₃₁ < SIZE₂₄
          || i₂₉ < SIZE₂₄
          || i₂₇ < SIZE₂₄
          || sum₃₄ == 0));


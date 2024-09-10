data c#void = c#void;

type c#ptr<a₀>;

type c#heap;

function c#bitxor(x₀: int, x₁: int): int;

function c#bitand(x₀: int, x₁: int): int;

function c#bitor(x₀: int, x₁: int): int;

goal {:named "assert"} (forall SIZE₄₀: int, a: [int]int, a₄₂: [int]int, i₄₃: int, i₄₅: int, i₄₇: int, i₄₉: int, i₅₁: int, i₅₃: int, i₅₅: int, i₅₇: int, sum₅₈: int, i₅₉: int ::
      (  -32768 <= SIZE₄₀
        && SIZE₄₀ < 32768
        && 1 < SIZE₄₀
        && 0 <= i₄₃
        && (forall i₅: int ::
              (  0 <= i₅
                && i₅ < i₄₃
                 ==> (exists nondet_short₁₄: int ::
                        -32768 <= nondet_short₁₄
                        && nondet_short₁₄ < 32768
                        && i₅ < SIZE₄₀
                        && a₄₂[i₅] == nondet_short₁₄)))
        && (forall i₅: int ::
                  0 <= i₅
                  && i₅ < i₄₃
                || a₄₂[i₅] == a[i₅])
        && 0 <= i₄₅
        && (forall i₉: int ::
              (  0 <= i₉
                && i₉ < i₄₅
                 ==> i₉ < SIZE₄₀))
        && 0 <= i₄₇
        && (forall i₁₃: int ::
              (  0 <= i₁₃
                && i₁₃ < i₄₇
                 ==> i₁₃ < SIZE₄₀))
        && 0 <= i₄₉
        && (forall i₁₇: int ::
              (  0 <= i₁₇
                && i₁₇ < i₄₉
                 ==> i₁₇ < SIZE₄₀))
        && 0 <= i₅₁
        && (forall i₂₁: int ::
              (  0 <= i₂₁
                && i₂₁ < i₅₁
                 ==> i₂₁ < SIZE₄₀))
        && 0 <= i₅₃
        && (forall i₂₅: int ::
              (  0 <= i₂₅
                && i₂₅ < i₅₃
                 ==> i₂₅ < SIZE₄₀))
        && 0 <= i₅₅
        && (forall i₂₉: int ::
              (  0 <= i₂₉
                && i₂₉ < i₅₅
                 ==> i₂₉ < SIZE₄₀))
        && 0 <= i₅₇
        && (forall i₃₃: int ::
              (  0 <= i₃₃
                && i₃₃ < i₅₇
                 ==> i₃₃ < SIZE₄₀))
        && 0 <= i₅₉
        && (forall i₃₇: int ::
              (  0 <= i₃₇
                && i₃₇ < i₅₉
                 ==> i₃₇ < SIZE₄₀))
         ==> i₅₉ < SIZE₄₀
          || i₅₇ < SIZE₄₀
          || i₅₅ < SIZE₄₀
          || i₅₃ < SIZE₄₀
          || i₅₁ < SIZE₄₀
          || i₄₉ < SIZE₄₀
          || i₄₇ < SIZE₄₀
          || i₄₅ < SIZE₄₀
          || i₄₃ < SIZE₄₀
          || sum₅₈ == 0));

